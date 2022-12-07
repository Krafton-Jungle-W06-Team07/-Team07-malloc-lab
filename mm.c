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
#define MIN 16
#define CHUNKSIZE (1 << 12)
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define PREC_FREEP(bp) (*(void **)(bp))
#define SUCC_FREEP(bp) (*(void **)(bp + WSIZE))
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

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
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
static char *heap_listp;
static char *listp;

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void put_list(void *bp);
static void remove_list(void *bp);

void remove_list(void *bp)
{
    if (bp == listp)
    { //가용 블록 리스트의 첫 부분을 삭제할때
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        listp = SUCC_FREEP(bp);
    }
    else
    { //가용 블록 리스트 중간에서 삭제할 때
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
    }
}
void put_list(void *bp)
{
    //가용 블록 리스트 맨 앞에 새로운 블록 넣기
    PREC_FREEP(bp) = NULL;
    SUCC_FREEP(bp) = listp;
    PREC_FREEP(listp) = bp;
    listp = bp;
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc)
    { /* Case 2 */
        remove_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
        remove_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && !next_alloc)
    { /* Case 4 */
        remove_list(NEXT_BLKP(bp));
        remove_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    put_list(bp);
    return bp;
}
static void *extend_heap(size_t words)
{
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
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1) //메모리 시스템에서 헤더,풋터,pred 포인터, succ 포인터를 넣을 6워드 가져오기
        return -1;
    PUT(heap_listp, 0); //미사용 패딩 워드
    PUT(heap_listp + (1 * WSIZE), PACK(MIN, 1)); //prologue 블록 헤더
    PUT(heap_listp + (2 * WSIZE), heap_listp + (3 * WSIZE)); //predecessor 포인터
    PUT(heap_listp + (3 * WSIZE), heap_listp + (2 * WSIZE)); //successor 포인터
    PUT(heap_listp + (4 * WSIZE), PACK(MIN, 1)); //prologue 블록 풋터
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1)); //epilogue 블록 
    listp = heap_listp + (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) //힙을 CHUNKSIZE로 확장
        return -1;
    return 0;
}

static void *find_fit(size_t asize)
{
    //가용 블록 리스트의 처음부터 탐색
    void *bp = listp;
    while (!GET_ALLOC(HDRP(bp)))
    {
        if (GET_SIZE(HDRP(bp)) >= asize) //asize를 넣을 수 있는 크기면
        {
            return bp; //반환
        }
        bp = SUCC_FREEP(bp); //다음 블록으로 이동
    }

    return NULL; //넣을 수 있는 가용블록이 없을 때
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_list(bp);
    if ((csize - asize) >= (2 * DSIZE)) //asize를 할당하고 남는 공간이 충분히 클때
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0)); //남는 공간을 가용 블록으로 설정해주고
        PUT(FTRP(bp), PACK(csize - asize, 0));
        put_list(bp); //가용 블록 리스트에 넣어주기
    }
    else //asize를 할당하고 남는 공간이 충분하지 않으면
    {
        //bp 블록 전체에 할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize; //맞는 가용 블록을 찾지 못했을 때 확장해줄 힙 크기
    char *bp;

    if (size == 0)
        return NULL;
    //오버헤드를 포함하고 정렬 조건을 만족하는 블록 사이즈
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) //할당할 가용 블록을 찾았을 때
    {
        place(bp, asize);
        return bp;
    }
    //맞는 가용 블록 찾지 못했을 때 메모리를 가져와서 할당
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

void *mm_realloc(void *ptr, size_t size)
{
    void *nextptr = NEXT_BLKP(ptr);
    size_t origin_size = GET_SIZE(HDRP(ptr)); //원래 사이즈
    size_t new_size = size + 8; //요청받은 사이즈에 헤더, 풋터 크기 더해주기
    if (origin_size >= new_size) //원래 사이즈보다 새로운 사이즈가 작거나 같을 때
    {
        return ptr; 
    }
    else
    {
        size_t add_size = GET_SIZE(HDRP(nextptr)) + origin_size; //원래블록사이즈 + 다음 블록 사이즈
        if(!GET_ALLOC(HDRP(nextptr)) && (add_size >= new_size)) //원래 블록의 다음 블록이 가용블록이면서 적당한 사이즈일때
        {
            remove_list(nextptr); //다음 블록을 가용블록리스트에서 삭제
            PUT(HDRP(ptr), PACK(add_size, 1));
            PUT(FTRP(ptr), PACK(add_size, 1));
            return ptr;
        }
        else
        {
            void *newptr = mm_malloc(new_size); //다른 공간에 새로 할당하고
            if(newptr == NULL) return NULL;
            memcpy(newptr, ptr, new_size); //복사해서 넣어주기
            mm_free(ptr); //원래 공간은 free
            return newptr;
        }
    }
}