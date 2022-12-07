#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "Team7",
    /* First member's full name */
    "su",
    /* First member's email address */
    "mail_1.jungle.com",
    /* Second member's full name (leave blank if none) */
    "ji",
    /* Second member's email address (leave blank if none) */
    "mail_2.jungle.com"
};

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12) // 4096bytes

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// CSAPP 순서
int mm_init(void);
static void *extend_heap(size_t words);
void mm_free(void *bp);
static void *coalesce(void *bp);
void *mm_malloc(size_t size);
static void place(void *bp, size_t adjusted_size);
void *mm_realloc(void *ptr, size_t size);

// 할당기 할당 방식. first, next, best
// first fit. Perf index = 44 (util) + 8 (thru) = 52(3)(4)/100. while 52점, for 53점, CSAPP 54점
// next fit. Perf index = 43 (util) + 40 (thru) = 83/100. realloc 개선 시 86점
// best fit. 
static void *first_fit(size_t adjusted_size);
static void *next_fit(size_t adjusted_size);
static void *best_fit(size_t adjusted_size);

// bp_pointer
static char *heap_listp;
static char *last_bp;       // next fit 에 이용. 가장 최근의 bp 위치

int mm_init(void) {
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));

    heap_listp += (2 * WSIZE);
    last_bp = heap_listp;

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

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // Case 1 첫 if문은 없어도 될 듯
    // if (prev_alloc && next_alloc) {
    //     last_bp = bp;
    //     return bp;
    // }
    if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc) {
        size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    last_bp = bp;
    return bp;
}

void *mm_malloc(size_t size) {
    size_t adjusted_size;
    size_t extend_size;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        adjusted_size = 2 * DSIZE;
    else
        adjusted_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // ⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂
    // ⁂⁂⁂⁂⁂⁂        할당 방식 선택. first, next, best       ⁂⁂⁂⁂⁂⁂
    // ⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂⁂
    // if ((bp = first_fit(adjusted_size)) != NULL)
    if ((bp = next_fit(adjusted_size)) != NULL)
    // if ((bp = best_fit(adjusted_size)) != NULL)
    {
        // last_bp = bp;
        place(bp, adjusted_size);

        return bp;
    }

    extend_size = MAX(adjusted_size, CHUNKSIZE);
    if ((bp = extend_heap(extend_size / WSIZE)) == NULL)
        return NULL;

    place(bp, adjusted_size);

    // last_bp = bp;
    return bp;
}

static void place(void *bp, size_t asize){  // asize = adjusted_size
    // 가용 블록 size
    size_t csize = GET_SIZE(HDRP(bp));

    // 분할 가능
    if ((csize - asize) >= (2*DSIZE)) {
        // (앞) 할당 블록
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // (뒤) 가용 블록
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr; // 크기 조절 힙 시작 포인터
    void *newptr;       // 크기 조절 뒤의 새 힙 시작 포인터
    size_t copySize;    // 복사할 힙 크기

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);

    return newptr;
}

// realloc 개선
void **improve_realloc(void *ptr, size_t size) {
    void *oldptr = ptr; // 크기 조절 힙 시작 포인터
    void *newptr;       // 크기 조절 뒤의 새 힙 시작 포인터
    size_t copySize;    // 복사할 힙 크기

    // if(siez > )

    return newptr;
}

static void *first_fit(size_t adjusted_size){

    char *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (adjusted_size <= GET_SIZE(HDRP(bp))))
            return bp;

    return NULL;
}

// 탐색 순서 : last_bp -> Epilogue header, 이후 heap_listp -> last_bp
static void *next_fit(size_t adjusted_size) {

    char *bp;

    // last_bp -> Epilogue header
    for (bp = last_bp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (adjusted_size <= GET_SIZE(HDRP(bp))))
            return bp;

    // heap_listp -> last_bp
    for (bp = heap_listp; bp != last_bp && GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (adjusted_size <= GET_SIZE(HDRP(bp))))
            return bp;

    return NULL;
}

static void *best_fit(size_t adjusted_size);