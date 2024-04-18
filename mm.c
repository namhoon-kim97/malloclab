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
    "Team - 3",
    /* First member's full name */
    "Lee Seong Ho",
    /* First member's email address */
    "lsh6451217@gmail.com",
    /* Second member's full name (leave blank if none) */
    "Jae Hyeok Jeung",
    /* Second member's email address (leave blank if none) */
    "zaqokm2@gmail.com"};

#define WSIZE 4             /* 워드와 header,footer 사이즈 (bytes)*/
#define DSIZE 8             /* double word (bytes) */
#define CHUNKSIZE (1 << 12) /* 확장될 힙의 크기 (bytes)*/

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(p) ((char *)(p)-WSIZE)
#define FTRP(p) ((char *)(p) + GET_SIZE(HDRP(p)) - DSIZE)

#define NEXT_BLKP(p) ((char *)(p) + GET_SIZE(HDRP(p)))
#define PREV_BLKP(p) ((char *)(p)-GET_SIZE(((char *)(p)-DSIZE)))

#define GET_SUCC(p) (*(void **)((char *)(p) + WSIZE))
#define GET_PRED(p) (*(void **)(p))

static char *heap_listp;

//함수 목록
static void *extend_heap(size_t words);

static void *coalesce(void *p);

static char *find_fit(size_t size);

static void place(void *p, size_t size);

static void remove_free_block(void *p);

static void add_free_block(void *p);

int mm_init(void) {
  if ((heap_listp = mem_sbrk(8 * WSIZE)) == (void *)-1)
    return -1;
  PUT(heap_listp, 0);
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
  heap_listp += (2 * WSIZE);

  return 0;
}

static void *extend_heap(size_t words) {
  char *p;
  size_t size;

  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(p = mem_sbrk(size)) == -1) //
    return NULL;

  PUT(HDRP(p), PACK(size, 0));         //헤더
  PUT(FTRP(p), PACK(size, 0));         //푸터
  PUT(HDRP(NEXT_BLKP(p)), PACK(0, 1)); // 에필로그 헤더 갱신해주기

  return coalesce(p);
}

/* 블록 할당 해제*/
static void *coalesce(void *p) {
  size_t prev_alloc =
      GET_ALLOC(FTRP(PREV_BLKP(p))) || (PREV_BLKP(p) == p); //이전 가용 상태
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(p)));
  size_t size = GET_SIZE(HDRP(p));

  if (prev_alloc && next_alloc) { // 둘다가용
    add_free_block(p);
    return p;
  } else if (prev_alloc && !next_alloc) { // 뒤만
    remove_free_block(NEXT_BLKP(p));
    size += GET_SIZE(HDRP(NEXT_BLKP(p)));
    PUT(HDRP(p), PACK(size, 0));
    PUT(FTRP(p), PACK(size, 0));
  } else if (!prev_alloc && next_alloc) { // 앞만
    size += GET_SIZE(HDRP(PREV_BLKP(p)));
    remove_free_block(PREV_BLKP(p));
    p = PREV_BLKP(p);
    PUT(HDRP(p), PACK(size, 0));
    PUT(FTRP(p), PACK(size, 0));
  } else { // 양쪽모두
    size += GET_SIZE(FTRP(NEXT_BLKP(p))) + GET_SIZE(HDRP(PREV_BLKP(p)));
    remove_free_block(NEXT_BLKP(p));
    remove_free_block(PREV_BLKP(p));
    p = PREV_BLKP(p);
    PUT(HDRP(p), PACK(size, 0));
    PUT(FTRP(p), PACK(size, 0));
  }
  add_free_block(p);
  return p;
}

// BEst Fit
static char *find_fit(size_t size) {
  void *p;
  void *best_fit = NULL;
  size_t min_remaining = 1 << 21; //가용 블록 사이즈의 차이가 가장 작은, 즉 남는
                                  //공간이 가장 적은 블록을 찾기 위함

  for (p = heap_listp; GET_ALLOC(HDRP(p)) == 0;
       p = GET_SUCC(p)) { //힙리스트 시작점
    if (size <= (size_t)GET_SIZE(HDRP(p))) {
      size_t remaining = (size_t)GET_SIZE(HDRP(p)) - size;
      if (remaining < min_remaining) {
        min_remaining = remaining; // 갱신 계속해서
        best_fit = p;
      }
    }
  }
  return best_fit;
}

static void remove_free_block(void *p) {
  if (GET_PRED(p) != NULL)
    GET_SUCC(GET_PRED(p)) = GET_SUCC(p);
  else
    heap_listp = GET_SUCC(p);
  GET_PRED(GET_SUCC(p)) = GET_PRED(p);
}

static void add_free_block(void *p) {
  GET_SUCC(p) = heap_listp;
  GET_PRED(heap_listp) = p;
  GET_PRED(p) = NULL;
  heap_listp = p;
}

static void place(void *p, size_t size) {
  size_t c_size = GET_SIZE(HDRP(p)); // 현재 블록의 크기

  remove_free_block(p); // 가용블록 연결 리스트에서 제거

  if ((c_size - size) >= (2 * DSIZE)) { //분할 기준
    PUT(HDRP(p), PACK(size, 1));
    PUT(FTRP(p), PACK(size, 1));

    p = NEXT_BLKP(p);

    PUT(HDRP(p), PACK(c_size - size, 0));
    PUT(FTRP(p), PACK(c_size - size, 0));
    add_free_block(p);
  } else {
    PUT(HDRP(p), PACK(c_size, 1));
    PUT(FTRP(p), PACK(c_size, 1));
  }
}

void *mm_malloc(size_t size) {
  size_t asize;
  size_t extendsize;
  char *p;

  if (size == 0)
    return NULL;

  if (size <= DSIZE)
    asize = 2 * DSIZE; /* size는 실제로 사용할 데이터 영역의 크기 -> header,
                          footer 포함하려면 DWORD 2배*/
  else
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

  if ((p = find_fit(asize)) != NULL) {
    place(p, asize); //할당 및 배치
    return p;
  }

  /* 맞는 블록이 없으면 힙 영역을 확장하고 요청 블록을 새 가용 블록에 배치 */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((p = extend_heap(extendsize / WSIZE)) == NULL)
    return NULL;
  place(p, asize);
  return p;
}

/*
 * mm_free : 할당 반환
 */
void mm_free(void *p) {
  size_t size = GET_SIZE(HDRP(p));

  PUT(HDRP(p), PACK(size, 0));
  PUT(FTRP(p), PACK(size, 0));
  coalesce(p);
}

/*
 * mm_realloc : 주소 p의 할당된 블록의 크기를 size 만큼 변경
 */
void *mm_realloc(void *p, size_t size) {
  if (size <= 0) {
    mm_free(p);
    return 0;
  }
  if (p == NULL)
    return mm_malloc(size);

  size_t new_size = size + 2 * WSIZE;
  size_t old_size = GET_SIZE(HDRP(p));
  size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(p)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(p)));
  size_t c_size;

  if (new_size <= old_size)
    return p;
  if (!prev_alloc &&
      new_size <= (c_size = old_size +
                            GET_SIZE(HDRP(PREV_BLKP(p))))) // 이전 블록과 통합
  {
    char *pre = PREV_BLKP(p);
    remove_free_block(pre);
    memmove(pre, p, old_size);
    PUT(HDRP(pre), PACK(c_size, 1));
    PUT(FTRP(pre), PACK(c_size, 1));
    return pre;
  }
  if (!next_alloc &&
      new_size <= (c_size = old_size +
                            GET_SIZE(HDRP(NEXT_BLKP(p))))) // 다음 블록과 통합
  {
    remove_free_block(NEXT_BLKP(p));

    PUT(HDRP(p), PACK(c_size, 1));
    PUT(FTRP(p), PACK(c_size, 1));
    return p;
  }

  void *newptr = mm_malloc(size);
  if (newptr == NULL)
    return 0;
  memcpy(newptr, p, old_size);
  mm_free(p);
  return newptr;
}