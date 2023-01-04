#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
inline static void assert(int e) {
  if (!e) {
    const char * msg = "Assertion Failed!\n";
    write(2, msg, strlen(msg));
    exit(1);
  }
}
#else
#include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t object_left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
  return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
  return get_header_from_offset(h, get_object_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->object_left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param object_left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t object_left_size) {
  set_object_state(fp,FENCEPOST);
  set_object_size(fp, ALLOC_HEADER_SIZE);
  fp->object_left_size = object_left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

static size_t max(size_t a, size_t b) {
  return ((a>b) ? (a) : (b));
}
static size_t min(size_t a, size_t b) {
  return (a < b) ? (a) : (b);
}
static size_t check_if_final(size_t k) {
  if (k > N_LISTS - 1) {
    k = N_LISTS - 1;
  }
  return k;
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);

  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_object_state(hdr, UNALLOCATED);
  set_object_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->object_left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

static inline header * ptr_to_freelist(size_t block_size);
static inline void delete(header * hdr);
static inline void insert(header * hdr);
static inline void insert_chunk();
static inline header * split(header * cur, size_t block_size);
static inline void update_freelist(header * old_hdr, header * new_hdr, size_t block_size);
static inline bool last_freelist(header * hdr);

static inline void insert_chunk() {
  header * block = allocate_chunk(ARENA_SIZE);
  header * prev = block;
  header * prev_FP = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  bool updated = false;

  // coalesce adjacent chunks
  if (((char *)prev_FP - ALLOC_HEADER_SIZE) == (char *) lastFencePost) {
    header * left_to_lastFP = get_left_header(lastFencePost);
    // Unallocated memory before last fence post.
    size_t left_block_size = 0;
    if (get_object_state(left_to_lastFP) == UNALLOCATED) {
      left_block_size = get_object_size(left_to_lastFP);
      if (last_freelist(left_to_lastFP)) {
        updated = true;
      } else {
        delete(left_to_lastFP);
      }
    }
    block = get_header_from_offset(lastFencePost, -left_block_size);
    set_object_size(block, 2*ALLOC_HEADER_SIZE + get_object_size(prev) + left_block_size);
    block->object_left_size = left_block_size? left_to_lastFP->object_left_size : lastFencePost->object_left_size;
    set_object_state(block, UNALLOCATED);
  } else {
    insert_os_chunk(prev_FP);
  }

  lastFencePost = get_header_from_offset(prev, get_object_size(prev));
  lastFencePost->object_left_size = get_object_size(block);

  // Insert chunk into the free list
  if (!updated){
    header * freelist = &freelistSentinels[N_LISTS - 1];
    block->next = freelist->next;
    freelist->next = block;
    block->next->prev = block;
    block->prev = freelist;
  }
}

static inline void delete(header * hdr) {
  int i = (get_object_size(hdr) - ALLOC_HEADER_SIZE)/sizeof(size_t)-1;
  i = i > (N_LISTS-1)? N_LISTS-1 : i;

  header * freelist = &freelistSentinels[i];
  for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
    if (cur == hdr) {
      cur->prev->next = cur->next;
      cur->next->prev = cur->prev;
    }
  }
}

static inline bool last_freelist(header * hdr){
  return get_object_size(hdr) >= (N_LISTS+2)*sizeof(size_t);
}

 static inline header * ptr_to_freelist(size_t block_size) {
  int idx = (int) (block_size - ALLOC_HEADER_SIZE) / sizeof(size_t) - 1;
  idx = idx < 58 ? idx : 58;
  for (int i = idx; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for(header * current = freelist->next; current != freelist; current = current->next) {
      if (get_object_size(current) > block_size) {
        return split(current, block_size);
      }
      if (get_object_size(current) == block_size){
        current->prev->next = current->next;
        current->next->prev = current->prev;
        return current;
      }
    }
  }
  return NULL;
}

static inline header * split(header * cur, size_t block_size) {
  if (get_object_size(cur) - block_size >= sizeof(header)) {
    set_object_size(cur, get_object_size(cur) - block_size);
    header * first = cur;
    cur = (header *)((char *)cur + get_object_size(cur));
    set_object_size(cur, block_size);
    // update the block
    cur->object_left_size = get_object_size(first);
    // update the block to the right
    header * right = (header *)((char *)cur + get_object_size(cur));
    right->object_left_size = get_object_size(cur);
    // put first into correct freelist
    if (get_object_size(first) < (N_LISTS+2) * sizeof(size_t)) {
      first->prev->next = first->next;
      first->next->prev = first->prev;
      insert(first);
    }
  }
  return cur;
}

static inline void insert(header * hdr) {
  int idx = (get_object_size(hdr) - ALLOC_HEADER_SIZE)/sizeof(size_t)-1;
  idx = idx > (N_LISTS-1)? N_LISTS-1 : idx;

  header * freelist = &freelistSentinels[idx];
  hdr->next = freelist->next;
  freelist->next = hdr;
  freelist->next->next->prev = hdr;
  hdr->prev = freelist;
}

static inline void update_freelist(header * old, header * new, size_t block_size) {
  set_object_size(new, block_size);
  new->next = old->next;
  new->prev = old->prev;
  old->next->prev = new;
  old->prev->next = old;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation
/*
  if (raw_size == 0) {
    return NULL;
  }

  size_t req_size = ((raw_size + 7) & (-8));
  size_t actual_size = max(req_size + ALLOC_HEADER_SIZE, sizeof(header));
  size_t alloc_size = actual_size - ALLOC_HEADER_SIZE;

  size_t i = min((alloc_size/8) - 1, N_LISTS - 1);
  for (i; i < N_LISTS; i++) {
    if (freelistSentinels[i].next == &freelistSentinels[i]) {
      continue;
    }
    // you are guaranteed a block of either equal or larger size here

    if (actual_size == get_object_size(freelistSentinels[i].next)) {
      // return the whole block
      header * b = freelistSentinels[i].next;
      set_object_state(b, ALLOCATED);
      freelistSentinels[i].next = &freelistSentinels[i];
      freelistSentinels[i].prev = &freelistSentinels[i];
      return (header *) b -> data;
    }
    else if (actual_size < get_object_size(freelistSentinels[i].next)) {
      header * b1 = (freelistSentinels[i].next);
      size_t block_size = get_object_size(freelistSentinels[i].next);
      size_t rem_size = block_size - actual_size;

      if (rem_size >= sizeof(header)) {

        // split
        header * b2 = get_header_from_offset(b1, rem_size);
        set_object_size(b2, actual_size);
        set_object_state(b2, ALLOCATED);
        b2 -> object_left_size = rem_size;
        set_object_size(b1, rem_size);
        get_right_header(b2) -> object_left_size = get_object_size(b2);

        if (rem_size < 512) {
          // update b1 pointer and place it in appropriate freelist
          size_t j = (rem_size - ALLOC_HEADER_SIZE)/8 - 1;
          j = check_if_final(j);
          freelistSentinels[j].next = b1;
          freelistSentinels[j].prev = b1;
          b1 -> next = &freelistSentinels[j];
          b1 -> prev = &freelistSentinels[j];
        }
        //return data
        return (header *) b2 -> data;
      }

      set_object_state(b1, ALLOCATED);
      freelistSentinels[i].next = &freelistSentinels[i];
      freelistSentinels[i].prev = &freelistSentinels[i];
      return (header *) b1 -> data;
    }
    else {
      // allocate more memory
      header * new_block = allocate_chunk(ARENA_SIZE);
      header * R_FP1 = lastFencePost;
      header * L_FP2 = get_header_from_offset(new_block, -ALLOC_HEADER_SIZE);
      if (R_FP1 + get_object_size(R_FP1) == L_FP2) {
        // adjacent
        new_block = R_FP1;
        size_t old_size = get_object_size(new_block);
        set_object_size(new_block, get_object_size(L_FP2) + get_object_size(R_FP1) + old_size);
        if (get_object_state(get_left_header(R_FP1)) == UNALLOCATED) {
          header * b3 = get_left_header(R_FP1);
          size_t final_size = get_object_size(b3) + get_object_size(new_block);
          set_object_size(b3, final_size);
          get_right_header(new_block) -> object_left_size = final_size;
          freelistSentinels[N_LISTS - 1].next = b3;
          freelistSentinels[N_LISTS - 1].prev = b3;
          b3 -> next = &freelistSentinels[N_LISTS - 1];
          b3 -> prev = &freelistSentinels[N_LISTS - 1];
        }
        else {
          freelistSentinels[N_LISTS - 1].next = new_block;
          freelistSentinels[N_LISTS - 1].prev = new_block;
          new_block -> next = &freelistSentinels[N_LISTS - 1];
          new_block -> prev = &freelistSentinels[N_LISTS - 1];
        }
      }
      else {
        insert_os_chunk(L_FP2);
      }
      lastFencePost = get_header_from_offset(new_block, get_object_size(new_block));
      header * mem = allocate_object(raw_size);
      return mem;
    }
  }
  // add recursive step for allocating more chunks here
*/

  size_t block_size = ((raw_size > (2*sizeof(size_t))? raw_size + ALLOC_HEADER_SIZE : sizeof(header)) + sizeof(size_t)-1) & ~(sizeof(size_t)-1);
  header * hdr = ptr_to_freelist(block_size);
  while (hdr == NULL) {
    insert_chunk();
    hdr = ptr_to_freelist(block_size);
  }

  set_object_state(hdr, ALLOCATED);

  return hdr;

}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation

  
  // check for null free
  if (p == NULL) {
    return;
  }
  /*
  header * block = ptr_to_header(p);

  // check for double free
  if ((get_object_state(block) == UNALLOCATED) || (get_object_state(block)) == FENCEPOST) {
    return;
  }

  if ((get_object_state(get_left_header(block)) == UNALLOCATED) && ((get_object_state(get_right_header(block)) == ALLOCATED) || (get_object_state(get_right_header(block)) == FENCEPOST))) {
    // left merge
    header * b1 = get_left_header(block);
    size_t final_size = get_object_size(b1) + get_object_size(block);
    set_object_size(b1, final_size);
    get_right_header(block) -> object_left_size = final_size;
    set_object_state(block, UNALLOCATED);

    size_t i = ((get_object_size(block) - ALLOC_HEADER_SIZE)/8) - 1;
    size_t j = ((get_object_size(b1) - ALLOC_HEADER_SIZE)/8) - 1;
    j = check_if_final(j);
    i = check_if_final(i);

    // remove right block from freelist
    freelistSentinels[i].next = &freelistSentinels[i];
    freelistSentinels[i].prev = &freelistSentinels[i];

    // insert coalesced block with new size into the appropriate freelist
    freelistSentinels[j].next = b1;
    freelistSentinels[j].prev = b1;
    b1 -> next = &freelistSentinels[j];
    b1 -> prev = &freelistSentinels[j];
  }

  else if ((get_object_state(get_right_header(block)) == UNALLOCATED) && ((get_object_state(get_left_header(block)) == ALLOCATED) || (get_object_state(get_left_header(block)) == FENCEPOST))) {
    // right merge
    header * b2 = get_right_header(block);
    size_t final_size = get_object_size(block) + get_object_size(b2);
    set_object_size(block, final_size);
    get_right_header(b2) -> object_left_size = final_size;
    set_object_state(block, UNALLOCATED);

    size_t i = ((get_object_size(b2) - ALLOC_HEADER_SIZE)/8) - 1;
    size_t j = ((get_object_size(block) - ALLOC_HEADER_SIZE)/8) - 1;
    i = check_if_final(i);
    j = check_if_final(j);

    // remove right block from freelist
    freelistSentinels[i].next = &freelistSentinels[i];
    freelistSentinels[i].prev = &freelistSentinels[i];

    // insert coalesced block into appropriate freelist
    freelistSentinels[j].next = block;
    freelistSentinels[j].prev = block;
    block -> next = &freelistSentinels[j];
    block -> prev = &freelistSentinels[j];
  }
  // check for the case where both left and right blocks are free as well

  else if ((get_object_state(get_right_header(block)) == UNALLOCATED) && ((get_object_state(get_left_header(block)) == UNALLOCATED))) {
    header * b1 = get_left_header(block);
    header * b2 = get_right_header(block);
    size_t final_size = get_object_size(b1) + get_object_size(block) + get_object_size(b2);
    set_object_size(b1, final_size);
    get_right_header(b2) -> object_left_size = final_size;
    set_object_state(block, UNALLOCATED);

    size_t a = ((get_object_size(b1) - ALLOC_HEADER_SIZE)/8) - 1;
    size_t b = ((get_object_size(b2) - ALLOC_HEADER_SIZE)/8) - 1;
    a = check_if_final(a);
    b = check_if_final(b);

    // remove left and right blocks from freelist
    freelistSentinels[b].next = &freelistSentinels[b];
    freelistSentinels[b].prev = &freelistSentinels[b];

    // insert coalesced block into appropriate freelist

    freelistSentinels[a].next = b1;
    freelistSentinels[a].prev = b1;
    b1 -> next = &freelistSentinels[a];
    b1 -> prev = &freelistSentinels[a];
  }

  // no merge
  else {
    set_object_state(block, UNALLOCATED);
    // insert block back to freelist
    size_t i = ((get_object_size(block) - ALLOC_HEADER_SIZE)/8) - 1;
    i = check_if_final(i);
    freelistSentinels[i].next = block;
    freelistSentinels[i].prev = block;
    block -> next = &freelistSentinels[i];
    block -> prev = &freelistSentinels[i];
  }
  set_object_state(block, UNALLOCATED);
  return;
  */

   header * hdr = ptr_to_header(p);

  // double free
  if (get_object_state(hdr) == UNALLOCATED) {
    fprintf(stderr, "Double Free Detected\n");
    assert(false);
    exit(1);
  }
  set_object_state(hdr, UNALLOCATED);

  // coalesce
  header * rightblock = (header *)((char *)hdr + get_object_size(hdr));
  header * leftblock = (header *)((char *)hdr - hdr->object_left_size);

  if (get_object_state(rightblock) == UNALLOCATED & get_object_state(leftblock) == UNALLOCATED) {
      size_t new_size = get_object_size(hdr) + get_object_size(leftblock) + get_object_size(rightblock);
      if (last_freelist(leftblock)) {
        delete(rightblock);
        set_object_size(leftblock, new_size);
      } else if (last_freelist(rightblock)) {
        delete(leftblock);
        update_freelist(rightblock, leftblock, new_size);
      } else {
        delete(leftblock);
        delete(rightblock);
        set_object_size(leftblock, new_size);
        insert(leftblock);
      }
      get_right_header(rightblock)->object_left_size = new_size;
  } else if (get_object_state(rightblock) == UNALLOCATED) {
    if (last_freelist(rightblock)) {
      update_freelist(rightblock, hdr, get_object_size(hdr) + get_object_size(rightblock));
    } else {
      delete(rightblock);
      set_object_size(hdr, get_object_size(hdr) + get_object_size(rightblock));
      insert(hdr);
    }
    rightblock = (header *)((char *)hdr + get_object_size(hdr));
    rightblock->object_left_size = get_object_size(hdr);
  } else if (get_object_state(leftblock) == UNALLOCATED) {
    if (last_freelist(leftblock)) {
      set_object_size(leftblock, get_object_size(hdr) + get_object_size(leftblock));
    } else {
      delete(leftblock);
      set_object_size(leftblock, get_object_size(hdr) + get_object_size(leftblock));
      insert(leftblock);
    }
    rightblock->object_left_size = get_object_size(leftblock);
  } else {
    insert(hdr);
  }
  set_object_state(hdr, UNALLOCATED);

}


/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
        fast != freelist; 
        slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
  if (get_object_state(chunk) != FENCEPOST) {
    fprintf(stderr, "Invalid fencepost\n");
    print_object(chunk);
    return chunk;
  }

  for (; get_object_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
    if (get_object_size(chunk)  != get_right_header(chunk)->object_left_size) {
      fprintf(stderr, "Invalid sizes\n");
      print_object(chunk);
      return chunk;
    }
  }

  return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_object_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
 if (!size) {
    return NULL;
  }
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return (header *)((char *)hdr + ALLOC_HEADER_SIZE);
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
