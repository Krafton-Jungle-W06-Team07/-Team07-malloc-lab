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
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

#include "mm.h"
#include "memlib.h"

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define MAX(x,y) ((x)>(y)? (x):(y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
static char* heap_listp;
/* 
 * mm_init - initialize the malloc package.
 */
static void *coalesce(void * bp){
    void * pre_hd = HDRP(PREV_BLKP(bp));
    void * next_hd = HDRP(NEXT_BLKP(bp));
    if (GET_ALLOC(pre_hd) && GET_ALLOC(next_hd)) return bp; //prev랑 next 모두 할당되어 있을 때
    if (!GET_ALLOC(pre_hd)) {
        if (!GET_ALLOC(next_hd)){ // prev랑 next 가용블록일 때
        PUT(HDRP(PREV_BLKP(bp)), PACK(GET_SIZE(HDRP(bp))+GET_SIZE(pre_hd)+GET_SIZE(next_hd), 0));
        PUT(FTRP(PREV_BLKP(bp)), PACK(GET_SIZE(HDRP(bp))+GET_SIZE(pre_hd)+GET_SIZE(next_hd), 0));
        }
        else{ // prev만 가용 블록일 때
        PUT(HDRP(PREV_BLKP(bp)) , PACK(GET_SIZE(HDRP(bp))+GET_SIZE(pre_hd), 0));
        PUT(FTRP(PREV_BLKP(bp)) , PACK(GET_SIZE(HDRP(bp))+GET_SIZE(pre_hd), 0));
        }
        bp = PREV_BLKP(bp);
    }
    else if(!GET_ALLOC(next_hd)){ // next만 가용 블록일 때
        PUT(HDRP(bp) , PACK(GET_SIZE(HDRP(bp))+GET_SIZE(next_hd), 0));
        PUT(FTRP(bp) , PACK(GET_SIZE(HDRP(bp))+GET_SIZE(next_hd), 0));
    }
    return bp;
}
static void * extend_heap(size_t words){
    size_t r_words = ceil(words / DSIZE / WSIZE); //words를 2word의 배수로 반올림
    void* bp = mem_sbrk(r_words * WSIZE); //추가적인 힙 공간 요청
    if (bp == (void *)-1) return NULL; //요청 실패
    PUT(HDRP(bp), PACK(r_words, 0)); //새 가용 블록 헤더
    PUT(FTRP(bp), PACK(r_words, 0)); //새 가용 블록 풋터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); //새 에필로그 블록

    return coalesce(bp);
}
int mm_init(void)
{
    heap_listp = mem_sbrk(4*WSIZE);
    if (heap_listp == (void*)-1) return -1;
    PUT(heap_listp, 0); //미사용 패딩 워드
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1)); //prologue 블록 헤더
    PUT(heap_listp + 2*WSIZE, PACK(DSIZE, 1)); //prologue 블록 풋터
    PUT(heap_listp + 3*WSIZE, PACK(0, 1)); //epilogue 블록 헤더
    heap_listp += 2*WSIZE; 

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
static void *find_fit(size_t asize)
{
    void* bp;
    for (bp = heap_listp; GET_SIZE(bp)>0; bp = NEXT_BLKP(bp))
    {
        if (GET_SIZE(bp)>= asize && GET_ALLOC(bp) == 0) return bp;
    }
    return NULL;
}
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)) - asize;
    if((csize >= 2 * DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize, 0));
        PUT(FTRP(bp), PACK(csize, 0));
    }
    else{
        PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));
        PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));
    }
}
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void* bp  = find_fit(newsize);
    if (bp != NULL)
    {
        place(bp, newsize);
        return bp;
    }
    else{
        bp = extend_heap(newsize/WSIZE);
        if ( bp == NULL) return NULL;
        place(bp, newsize);
        return bp;
    }
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














