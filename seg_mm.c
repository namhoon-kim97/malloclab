/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "2team",
    /* First member's full name */
    "Namhoon Kim",
    /* First member's email address */
    "kskcmh5723@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/*Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and writed a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read thesize and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

#define PREV_FREE(bp) (*(void **)(bp))
#define NEXT_FREE(bp) (*(void **)(bp + WSIZE))

#define SEG_SIZE 20
#define SEG_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))

static char *heap_listp; /* Points to the start of the heap */

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void remove_freeblock(void *bp);
static void put_freeblock(void *bp);
static unsigned int seg_find(size_t size);

/*
 * mm_init - initialize the malloc package.
 */

int mm_init(void) {
  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk((SEG_SIZE + 4) * WSIZE)) == (void *)-1)
    return -1;
  PUT(heap_listp, 0); /* paddig word */
  PUT(heap_listp + (1 * WSIZE),
      PACK(WSIZE * (SEG_SIZE + 2), 1)); /* prologue header */
  for (int i = 0; i < SEG_SIZE; i++)
    PUT(heap_listp + ((i + 2) * WSIZE), PACK(0, 0)); /* initialize seg list */

  PUT(heap_listp + (SEG_SIZE + 2) * WSIZE,
      PACK((WSIZE * (SEG_SIZE + 2)), 1));               /* prologue footer */
  PUT(heap_listp + (SEG_SIZE + 3) * WSIZE, PACK(0, 1)); /* epilogue header */
  heap_listp += (2 * WSIZE);

  extend_heap(4);

  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    return -1;
  return 0;
}

static void *extend_heap(size_t words) {
  char *bp;
  size_t size;

  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;

  PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

  /* Coalesce if the previous block was free */
  return coalesce(bp);
}

static unsigned int seg_find(size_t size) {
  int i = 0;
  int bound = SEG_SIZE - 1;
  while ((i < bound) && (size > 1)) {
    size >>= 1;
    i++;
  }

  return i;
}

static void *find_fit(size_t asize) {
  int idx = seg_find(asize);
  void *ptr = NULL;

  // 검색 시작 인덱스에서 SEG_SIZE까지 루프를 수행
  while (idx < SEG_SIZE) {
    ptr = SEG_ROOT(idx); // 현재 인덱스에 해당하는 리스트의 루트.
    while (ptr && (asize > GET_SIZE(HDRP(ptr)))) {
      ptr = PREV_FREE(ptr); // 이전 가용 블록으로 이동
    }
    if (ptr) { // 적절한 블록을 찾았으면 반복 중단
      break;
    }
    idx++; // 다음 세그먼트 리스트로 이동
  }

  return ptr;
}

static void remove_freeblock(void *bp) {
  unsigned int idx = seg_find(GET_SIZE(HDRP(bp)));

  if (PREV_FREE(bp)) {
    if (NEXT_FREE(bp)) {
      NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
      PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
    } else {
      NEXT_FREE(PREV_FREE(bp)) = NULL;
      SEG_ROOT(idx) = PREV_FREE(bp);
    }
  } else {
    if (NEXT_FREE(bp))
      PREV_FREE(NEXT_FREE(bp)) = NULL;
    else
      SEG_ROOT(idx) = NULL;
  }

  return;
}

static void place(void *bp, size_t asize) {
  size_t csize = GET_SIZE(HDRP(bp));

  remove_freeblock(bp);
  if ((csize - asize) >= (2 * DSIZE)) { /* 할당할 크기보다 블록 사이즈가 큰 경우
                                           나머지를 가용블록으로 쪼갬 */
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));

    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    put_freeblock(bp);
  } else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}

static void put_freeblock(void *bp) {
  size_t size = GET_SIZE(HDRP(bp));
  unsigned int idx = seg_find(size);
  char *search_ptr = SEG_ROOT(idx);
  char *insert_ptr = NULL;

  while (search_ptr && (size > GET_SIZE(HDRP(search_ptr)))) {
    insert_ptr = search_ptr;
    search_ptr = PREV_FREE(search_ptr);
  }

  if (search_ptr) {
    PREV_FREE(bp) = search_ptr;
    NEXT_FREE(search_ptr) = bp;
    if (insert_ptr) { /* insert_ptr과 search_ptr사이에 bp 삽입 */
      NEXT_FREE(bp) = insert_ptr;
      PREV_FREE(insert_ptr) = bp;
    } else { /* 맨 처음(루트)에 bp 삽입 */
      NEXT_FREE(bp) = NULL;
      SEG_ROOT(idx) = bp;
    }
  } else {
    PREV_FREE(bp) = NULL;
    if (insert_ptr) { /* 리스트의 끝에 bp 삽입 */
      NEXT_FREE(bp) = insert_ptr;
      PREV_FREE(insert_ptr) = bp;
    } else { /* 맨 처음(루트)에 bp 삽입 */
      NEXT_FREE(bp) = NULL;
      SEG_ROOT(idx) = bp;
    }
  }
}

void *mm_malloc(size_t size) {
  size_t asize;
  size_t extendsize;
  char *bp;

  if (size == 0)
    return NULL;

  if (size <= DSIZE)
    asize = 2 * DSIZE;
  else
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

  bp = find_fit(asize);
  if (!bp) {
    extendsize = MAX(asize, CHUNKSIZE); /* 가용 블록을 못찾았다면*/
    if (!(bp = extend_heap(extendsize / WSIZE))) /* heap_size를 늘려줘야 함 */
      return NULL;
  }
  place(bp, asize);
  return bp;
}

static void *coalesce(void *bp) {
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && !next_alloc) { // next 연결
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    remove_freeblock(NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  } else if (!prev_alloc && next_alloc) { // prev 연결
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    remove_freeblock(PREV_BLKP(bp));
    bp = PREV_BLKP(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  } else if (!prev_alloc && !next_alloc) { // next, prev 연결
    size += GET_SIZE(FTRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
    remove_freeblock(PREV_BLKP(bp));
    remove_freeblock(NEXT_BLKP(bp));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  put_freeblock(bp);
  return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));

  coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */

void *mm_realloc(void *ptr, size_t size) {
  void *oldptr = ptr;
  void *newptr;
  size_t copySize;

  newptr = mm_malloc(size);
  if (newptr == NULL)
    return NULL;
  copySize = GET_SIZE(HDRP(ptr));
  if (size < copySize)
    copySize = size;
  memcpy(newptr, oldptr, copySize);
  mm_free(oldptr);
  return newptr;
}