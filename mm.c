/*
 * Author: Daniel Marczak (324351)
 * mm.c - Implementation using LIFO, boundertags,
 * best-fit strategies and optimized realloc.
 *
 * Solution based on lecture presentation,
 * CSAPP book and solution template from mm-implicit.c file.
 */
#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

#define __unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0, /* Block is free */
  USED = 1, /* Block is used */
} bt_flags;

static word_t *heap_start;    /* Address of the first block */
static word_t *bt_heap_last;  /* Boundery tag of the last block */
static word_t *bt_heap_start; /* Boundary tag of the first block */

/* --=[ boundary tag handling ]=-------------------------------------------- */

/* Given boundary tag address calculate the block size in bytes*/
static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED);
}

/* Given boundary tag address returns whether the block is in use */
static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

/* Given boundary tag address returns whether the block is free */
static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  *bt = ((word_t)size) | flags;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  if (bt_size(bt) == 0) {
    return NULL;
  }
  return (word_t *)(bt + (bt_size(bt) / 4));
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  if (bt_payload(bt) == bt_fromptr(heap_start)) {
    return NULL;
  }
  return (word_t *)(bt - (bt_size(bt - 1) / 4));
}

/* --=[ LIFO handling ]=----------------------------------------------------- */

/* Given boundary tag return distance to next LIFO block */
static inline word_t lifo_get_next(word_t *bt) {
  return *(bt + 1);
}

/* Given boundary tag return distance to previous LIFO block */
static inline word_t lifo_get_prev(word_t *bt) {
  return *(bt + 2);
}

/* Set next LIFO block to value p */
static inline void lifo_put_next(word_t *bt, word_t p) {
  *(bt + 1) = p;
}

/* Set previous LIFO block to value p */
static inline void lifo_put_prev(word_t *bt, word_t p) {
  *(bt + 2) = p;
}

/* Create next pointer of LIFO in current_bt */
static void lifo_create_next(word_t *current_bt, word_t *next_bt) {
  word_t value =
    (word_t)(next_bt -
             current_bt); /* Distance in block between current_bt and next_bt */
  lifo_put_next(current_bt, value); /* Put distance in current_bt */
}
/* Create previous pointer of LIFO in current_bt */
static void lifo_create_prev(word_t *current_bt, word_t *prev_bt) {
  word_t value =
    (word_t)(prev_bt -
             current_bt); /* Distance in block between current_bt and prev_bt */
  lifo_put_prev(current_bt, value);
}

/* Given boundary tag returns boundary tag of next LIFO block or NULL if it is
 * the last block in LIFO */
static word_t *lifo_next(word_t *bt) {
  word_t distance = lifo_get_next(bt);
  if (distance == 0) {
    return NULL;
  }
  word_t *next_bt = bt + distance;
  return next_bt;
}

/* Given boundary tag returns boundary tag of previous LIFO block or NULL if it
 * is the block in LIFO */
static word_t *lifo_prev(word_t *bt) {
  word_t distance = lifo_get_prev(bt);
  if (distance == 0) {
    return NULL;
  }
  word_t *prev_bt = bt + distance;
  return prev_bt;
}

/* Connect two blocks in LIFO */
static void lifo_connect(word_t *current_bt, word_t *next_bt) {
  lifo_create_next(current_bt, next_bt);
  lifo_create_prev(next_bt, current_bt);
}

/* Put block to LIFO */
static void lifo_add(word_t *current_bt) {
  word_t *next_bt = lifo_next(bt_heap_start);
  lifo_create_next(current_bt, next_bt);
  lifo_create_prev(current_bt, bt_heap_start);
  lifo_create_next(bt_heap_start, current_bt);
  lifo_create_prev(next_bt, current_bt);
}

/* --=[ mm_init ]=---------------------------------------------------------- */

/* Coalesce free blocks. */
static void *coalesce(void *ptr) {
  word_t *current_bt = bt_fromptr(ptr);
  word_t *prev_bt = bt_prev(current_bt);
  word_t *next_bt = bt_next(current_bt);

  size_t size = bt_size(current_bt);
  /* Case 1 */
  if (bt_used(prev_bt) && (bt_heap_last == current_bt || bt_used(next_bt))) {
    lifo_add(current_bt);
    return ptr;
  }
  /* Case 2 */
  else if (bt_used(prev_bt) &&
           (bt_heap_last != current_bt && bt_free(next_bt))) {
    size += bt_size(next_bt);
    lifo_connect(lifo_prev(next_bt), lifo_next(next_bt));
    bt_make(current_bt, size, FREE);
    bt_make(bt_footer(current_bt), size, FREE);
    lifo_add(current_bt);
    if (bt_heap_last == next_bt) {
      bt_heap_last = current_bt;
    }
  }
  /* Case 3 */
  else if (bt_free(prev_bt) &&
           (bt_heap_last == current_bt || bt_used(next_bt))) {
    size += bt_size(prev_bt);
    lifo_connect(lifo_prev(prev_bt), lifo_next(prev_bt));
    bt_make(bt_footer(current_bt), size, FREE);
    bt_make(prev_bt, size, FREE);
    lifo_add(prev_bt);
    ptr = bt_payload(prev_bt);
    if (bt_heap_last == current_bt) {
      bt_heap_last = prev_bt;
    }
  }
  /* Case 4 */
  else {
    size += bt_size(prev_bt) + bt_size(next_bt);
    lifo_connect(lifo_prev(prev_bt), lifo_next(prev_bt));
    lifo_connect(lifo_prev(next_bt), lifo_next(next_bt));
    bt_make(prev_bt, size, FREE);
    bt_make(bt_footer(next_bt), size, FREE);
    lifo_add(prev_bt);
    ptr = bt_payload(prev_bt);
    if (bt_heap_last == next_bt) {
      bt_heap_last = prev_bt;
    }
  }
  return ptr;
}

int mm_init(void) {
  /* Create the initial empty heap */
  if ((heap_start = mem_sbrk(12 * sizeof(word_t))) == (void *)-1) {
    return -1;
  }

  /* First block of LIFO */
  bt_make(heap_start + 3, ALIGNMENT,
          USED); /* Header of the first block of LIFO */
  bt_make(heap_start + 6, ALIGNMENT,
          USED); /* Footer of the first block of LIFO */
  lifo_create_next(
    heap_start + 3,
    heap_start +
      7); /* Distance to the last block of LIFO is in 2 word of the block*/
  *(heap_start + 5) =
    0; /* First block of LIFO don't have previous block in LIFO */

  /* Last block of LIFO */
  bt_make(heap_start + 7, ALIGNMENT,
          USED); /* Header of the last block of LIFO */
  bt_make(heap_start + 10, ALIGNMENT,
          USED);         /* Footer of the last block of LIFO */
  *(heap_start + 8) = 0; /* First block of LIFO don't have next block in LIFO */
  lifo_create_prev(
    heap_start + 7,
    heap_start +
      3); /* Distance to the first block of LIFO is in 3 word of the block*/

  heap_start += 4;
  bt_heap_start = bt_fromptr(heap_start);
  bt_heap_last = bt_heap_start + 4;
  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

#if 0
/* First fit startegy. */
static word_t *find_fit(size_t reqsz) {
  word_t * current_block = lifo_next(bt_heap_start);
  while (current_block != NULL && (bt_used(current_block) || (bt_size(current_block) < reqsz))) {
    current_block = lifo_next(current_block);
  }
  return current_block;
}
#else
/* Best fit startegy. */
static word_t *find_fit(size_t reqsz) {
  word_t *current_block = lifo_next(bt_heap_start);
  word_t *result = NULL;
  size_t result_size = 0;
  while (current_block != NULL) {
    if (bt_free(current_block) && bt_size(current_block) >= reqsz) {
      if (result == NULL) {
        result = current_block;
        result_size = bt_size(current_block);
      } else if (result_size > bt_size(current_block)) {
        result = current_block;
        result_size = bt_size(current_block);
      }
    }
    current_block = lifo_next(current_block);
  }
  return result;
}
#endif

/* Split free block */
static void place(word_t *bt, size_t asize) {
  size_t csize = bt_size(bt);
  if ((csize - asize) >= 16) {
    bt_make(bt, asize, USED);
    bt_make(bt_footer(bt), asize, USED);
    word_t *bt_new = bt_next(bt);
    lifo_connect(lifo_prev(bt), bt_new);
    lifo_connect(bt_new, lifo_next(bt));
    bt_make(bt_new, (csize - asize), FREE);
    bt_make(bt_footer(bt_new), (csize - asize), FREE);
    if (bt == bt_heap_last) {
      bt_heap_last = bt_new;
    }
  } else {
    lifo_connect(lifo_prev(bt), lifo_next(bt));
    bt_make(bt, csize, USED);
    bt_make(bt_footer(bt), csize, USED);
  }
}

static void *extend_heap(size_t size) {
  word_t *bt;
  word_t *ptr;
  size_t round_size;

  /* Maintain alignment */
  round_size = (size + ALIGNMENT - 1) & -ALIGNMENT;

  /* Allocate */
  if ((ptr = mem_sbrk(round_size)) == (word_t *)-1) {
    return NULL;
  }
  bt = bt_fromptr(ptr);
  /* Initialize free block header/footer and the epilogue header */
  bt_make(bt, round_size, FREE);            /* Free block header */
  bt_make(bt_footer(bt), round_size, FREE); /* Free block footer */
  bt_heap_last = bt;
  /* Coalesce if the previous block was free */
  return coalesce(ptr);
}

void *malloc(size_t size) {
  // printf("m\n");
  size_t asize;
  size_t extendsize;
  word_t *bt;

  /* Ignore spurious requests */
  if (size == 0) {
    return NULL;
  }

  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= 8) {
    asize = 16;
  } else {
    asize = (ALIGNMENT * ((size + 8 + ALIGNMENT - 1) / ALIGNMENT));
  }
  /* Search the free list for a fit */
  if ((bt = find_fit(asize)) != NULL) {
    place(bt, asize);
    return bt_payload(bt);
  }
  /* No fit found. Get more memory and place the block */
  extendsize = asize;
  void *ptr;
  if ((ptr = extend_heap(extendsize)) == NULL) {
    return NULL;
  }
  bt = bt_fromptr(ptr);
  place(bt, asize);
  return bt_payload(bt);
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
  if (ptr == NULL) {
    return;
  }
  word_t *bt = bt_fromptr(ptr);
  size_t size = bt_size(bt);
  bt_make(bt, size, FREE);
  bt_make(bt_footer(bt), size, FREE);
  coalesce(ptr);
}

/* --=[ realloc ]=---------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  size_t asize;
  if (size <= 8) {
    asize = 16;
  } else {
    asize = (ALIGNMENT * ((size + 8 + ALIGNMENT - 1) / ALIGNMENT));
  }
  word_t *current_bt = bt_fromptr(old_ptr);
  word_t *next_bt = NULL;
  size_t old_size = bt_size(current_bt);
  size_t new_size = 0;
  if (current_bt != bt_heap_last) {
    next_bt = bt_next(current_bt);
    if (bt_free(next_bt)) {
      new_size = old_size + bt_size(next_bt);
    } else {
      next_bt = NULL;
    }
  }

  if (asize == old_size) {
    return old_ptr;
  } else if (asize < old_size) {
    size_t csize = bt_size(current_bt);
    if ((csize - asize) >= 16) {
      bt_make(current_bt, asize, USED);
      bt_make(bt_footer(current_bt), asize, USED);
      word_t *bt_new = bt_next(current_bt);
      bt_make(bt_new, (csize - asize), FREE);
      bt_make(bt_footer(bt_new), (csize - asize), FREE);

      if (current_bt == bt_heap_last) {
        bt_heap_last = bt_new;
      }

      lifo_add(bt_new);
    }
    return old_ptr;
  } else if (next_bt != NULL && asize <= new_size) {
    if ((new_size - asize) >= 16) {
      bt_make(current_bt, asize, USED);
      word_t *bt_new = bt_next(current_bt);
      lifo_connect(lifo_prev(next_bt), bt_new);
      lifo_connect(bt_new, lifo_next(next_bt));
      bt_make(bt_footer(current_bt), asize, USED);
      bt_make(bt_new, (new_size - asize), FREE);
      bt_make(bt_footer(bt_new), (new_size - asize), FREE);
      if (next_bt == bt_heap_last) {
        bt_heap_last = bt_new;
      }
    } else {
      lifo_connect(lifo_prev(next_bt), lifo_next(next_bt));
      bt_make(current_bt, new_size, USED);
      bt_make(bt_footer(current_bt), new_size, USED);
      if (next_bt == bt_heap_last) {
        bt_heap_last = current_bt;
      }
    }
    return old_ptr;
  } else {
    void *new_ptr = malloc(size);
    if (!new_ptr)
      return NULL;
    memcpy(new_ptr, old_ptr, old_size - 8);
    free(old_ptr);
    return new_ptr;
  }
}

/* --=[ calloc ]=----------------------------------------------------------- */

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */

void mm_checkheap(int verbose) {
}
