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

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "RedTeam07",
    /* First member's full name */
    "olive-su",
    /* First member's email address */
    "1466su@gmail.com",
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

/* 기본 상수와 매크로 */
#define WSIZE 4 // 워드(4byte) 와 헤더, 푸터 사이즈
#define DSIZE 8 // 더블 워드(8byte) 사이즈
#define CHUNKSIZE (1 << 12) // 초기 가용 블록과 힙 확장을 위한 기본 크기 (1_000_000_000_000)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 가용 리스트에 접근하고 방문하는 작은 매크로들 */
#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합 -> 헤더와 푸터에 저장

#define GET(p) (*(unsigned int *)(p)) // p가 참조하는 워드 리턴 / 인자 p는 (void*) 이므로 역참조는 불가하다.
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // p에 val을 저장

#define GET_SIZE(p) (GET(p) & ~0x7) // 헤더 또는 푸터의 사이즈 리턴
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당 비트 리턴

#define HDRP(bp) ((char *)(bp) - WSIZE) // 블록 헤더를 가리키는 포인터 리턴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록 푸터를 가리키는 포인터 리턴 
// ↳ HDRP(bp)에 헤더 사이즈(w)도 포함되어 있어서 DSIZE를 빼준다.

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 포인터
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 포인터

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *first_fit(size_t asize);
static void *next_fit(size_t asize);
static void *best_fit(size_t asize);
static void place(void *bp, size_t asize);

static char *heap_listp;  
static char *next_heap_listp;


/******    메인 함수    ******/

/**
 * @brief mm_init - initialize the malloc package.
 * @details 초기화를 완료하고 할당과 반환 요청을 받을 준비 완료
 * 
 * @param void
 * @return int   
 */
int mm_init(void)
{
    heap_listp = mem_sbrk(4 * WSIZE); // 초기 상태를 저장하기 위한 사이즈 지정

    if (heap_listp == (void *)-1) // 오류 (sbrk와 동일)
        return -1;

    // 1. 빈 가용 리스트를 만들 수 있도록 초기화한다.
    PUT(heap_listp, 0); // 미사용 패딩 워드
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // 에필로그 헤더
    heap_listp += (2*WSIZE); // heap_listp 위치를 프롤로그 헤더 뒤로 옮긴다.
    next_heap_listp = heap_listp; // next_fit에서 사용하기 위해 초기 포인터 위치를 넣어준다.

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) // 2. 이후 일반 블록을 저장하기 위해 힙을 확장한다.
        return -1;

    return 0;
}


/**
 * @brief mm_malloc - Allocate a block by incrementing the brk pointer. @n   Always allocate a block whose size is a multiple of the alignment.
 * @details 새 블록 할당
 * 
 * @param size_t size 새로 할당하려는 블록의 바이트 수 
 * @return void* 
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) // 사이즈 0 요청 처리
        return NULL;

    // 더블 워드 정렬 제한 조건을 만족 시키기위해 더블 워드 단위로 크기를 설정한다.    
    if (size <= DSIZE) // 최소 크기인 16바이트(헤더, 푸터, 페이로드 포함)로 설정한다.
        asize = 2 * DSIZE;
    else // 8바이트를 넘는 요청 처리
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // 조정한 크기(asize)에 대해 가용 리스트에서 적절한 가용 블록을 찾는다.
    bp = next_fit(asize); // Choice fit-method : first_fit, next_fit, best_fit

    if (bp != NULL) {
        place(bp, asize); // 초과부분을 분할한다.
        next_heap_listp = bp;
        return bp; // 새롭게 할당한 블록을 리턴한다.
    }

    // 적합한 fit 공간을 찾지 못했을 때 heap을 확장한다.
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    next_heap_listp = bp;
    return bp;
}

/**
 * @brief mm_free - Freeing a block does nothing.
 * @details 요청한 블록 반환
 * 
 * @param void* ptr 반환하려는 블록 포인터 
 * @return void
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr)); // 반환하려는 블록의 사이즈

    PUT(HDRP(ptr), PACK(size, 0)); // 헤더의 할당 비트를 0으로 설정한다.
    PUT(FTRP(ptr), PACK(size, 0)); // 헤더의 할당 비트를 0으로 설정한다.
    coalesce(ptr); // 인접 가용 블록들에 대한 연결을 수행한다.
}

/**
 * @brief mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * @details 할당 블록 크기 재조정
 * 
 * @param void* ptr 이전 메모리 포인터 
 * @param size_t size 조정하려는 메모리 사이즈(기존 사이즈보다 작을 수도 있다.)
 * @return void* 
 */

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr; // 이전 포인터
    void *newptr; // 새로 메모리 할당할포인터

    size_t originsize = GET_SIZE(HDRP(oldptr)); // 원본 사이즈
    size_t newsize = size + DSIZE; // 새 사이즈

    // size 가 더 작은 경우
    if (newsize <= originsize) { 
        return oldptr;
    } else {
        size_t addSize = originsize + GET_SIZE(HDRP(NEXT_BLKP(oldptr))); // 추가 사이즈 -> 헤더 포함 사이즈
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (newsize <= addSize)){ // 가용 블록이고 사이즈 충분
            PUT(HDRP(oldptr), PACK(addSize, 1)); // 새로운 헤더
            PUT(FTRP(oldptr), PACK(addSize, 1)); // 새로운 푸터
            return oldptr;
        } else {
            newptr = mm_malloc(newsize);
            if (newptr == NULL)
                return NULL;
            memmove(newptr, oldptr, newsize); // memcpy 사용 시, memcpy-param-overlap 발생
            mm_free(oldptr);
            return newptr;
        }
    }
}


/******    서브 함수    ******/

/**
 * @brief 힙의 크기를 확장한다.
 * 
 * @param size_t words 확장하려는 워드 개수
 * @return void* 새로 생긴 가용 블록의 포인터
 */
static void *extend_heap(size_t words)
{   
    char *bp; // 블록 포인터
    size_t size;

    // 더블 워드 정렬 제한 조건을 적용하기 위해 반드시 짝수 사이즈(8byte)의 메모리만 할당한다.(반올림)
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; 
    bp = mem_sbrk(size); // mem_sbrk return : 이전 brk(epilogue block 뒤 포인터) 반환
    // ↳ 실제 brk : 확장 후 힙의 맨 끝 포인터

    if ((long)bp ==  -1) // mem_sbrk err return
        return NULL;

    PUT(HDRP(bp), PACK(size, 0)); // size 만큼의 가용 블록의 헤더를 생성한다.
    PUT(FTRP(bp), PACK(size, 0)); // size 만큼의 가용 블록의 푸터를 생성한다.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새로운 에필로그 헤더를 생성한다.

    return coalesce(bp); // 이전 힙이 가용 블록이라면 연결 수행
}

/**
 * @brief 인접 가용 블록들을 연결한다.
 * 
 * @param void* bp 블록 포인터
 * @return void* 통합된 블록 포인터
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 푸터에서 할당 여부 파악
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 헤더에서 할당 여부 파악
    size_t size = GET_SIZE(HDRP(bp)); // (할당 비트를 제외한) 블록 사이즈

    // @pb : 이전 블록, @cb : 현재 블록, @nb : 다음 블록
    // [CASE 1] : pb, nb - 둘 다 할당 상태
    if (prev_alloc && next_alloc) 
    {
        return bp;
    }
    // [CASE 2] : pb - 할당 상태 / nb - 가용 상태
    // resize block size : cb + nb 
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 현재 블록 사이즈에 다음 블록 사이즈 더함
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // [CASE 3] : pb - 가용 상태 / nb - 할당 상태
    // resize block size : pb + cb 
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // [CASE 4] : pb - 가용 상태 / nb - 가용 상태
    // resize block size : pb + nb 
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // next_heap_listp가 속해있는 블록이 이전 블록과 합쳐진다면 
    // next_heap_listp에 해당하는 블록을 찾아갈 수 없으므로
    // 새로 next_heap_listp를 이전 블록 위치로 지정해준다.
    next_heap_listp = bp; 
    return bp;
}

/**
 * @brief first-fit 방식으로 가용 블록 탐색
 * 
 * @param size_t asize 새로 할당하려는 블록 바이트 수
 * @return void* 
 */
static void *first_fit(size_t asize)
{
    void *bp;

    // 에필로그 블록의 헤더를 0으로 넣어줬으므로 에필로그 블록을 만날 때까지 탐색을 진행한다.
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    
    return NULL;
}

/**
 * @brief next-fit 방식으로 가용 블록 탐색
 * 
 * @param size_t asize 새로 할당하려는 블록 바이트 수
 * @return void* 
 */
static void *next_fit(size_t asize)
{
    char *bp;

    // next_fit 포인터에서 탐색을 시작한다.
    for (bp = NEXT_BLKP(next_heap_listp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    
    for (bp = heap_listp; bp <= next_heap_listp; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;

    return NULL;
}

/**
 * @brief best-fit 방식으로 가용 블록 탐색
 * 
 * @param size_t asize 새로 할당하려는 블록 바이트 수
 * @return void* 
 */
static void *best_fit(size_t asize)
{
    void *bp;
    void *best_fit = NULL;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            // 기존에 할당하려던 공간보다 더 최적의 공간이 나타났을 경우 리턴 블록 포인터 갱신
            if (!best_fit || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_fit))) 
                best_fit = bp;
    
    return best_fit;
}

/**
 * @brief 가용 블록 분할(할당 블록 / 가용 블록) 
 * 
 * @param void* bp 블록 포인터 
 * @param size_t asize 새로 할당하려는 블록 바이트 수
 * @return void
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 가용 블록의 사이즈

    if ((csize - asize) >= (2 * DSIZE)) {
        // asize만큼의 할당 블록을 생성한다.
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        next_heap_listp = bp; // 분할 이후 그 다음 블록
        // 새로운 할당 블록(전체 가용 블록 - 할당 블록)의 뒷 부분을 가용 블록으로 만든다.
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        next_heap_listp = NEXT_BLKP(bp); // 분할 이후 그 다음 블록
    }
}
