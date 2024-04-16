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
    "team1",
    /* First member's full name */
    "Terry Ahn",
    /* First member's email address */
    "t3rryahn.dev@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
 * macro
 */

#define WSIZE   4                   // word size (bytes)
#define DSIZE   8                   // double word size (bytes)
#define CHUNKSIZE       (1 << 12)   // increase heap size to 4KB (4096 bytes) 메모리 페이지 크기가 4KB

#define MAX(x, y)       ((x) > (y) ? (x) : (y))

// pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc)) // size + block available. OR 연산으로 헤더에 넣을 정보를 만듬 사이즈 + 가용여부(끝 3자리)

// Read and write a word at address p
#define GET(p)          (*(unsigned int *)(p))
#define PUT(p, val)     (*(unsigned int *)(p) = (int)(val))

// Read the size and allocated fields from address p
#define GET_SIZE(p)     (GET(p) & ~0x7)     // 00000111 의 보수(~) 를 취해서 11111000 을 가져와 AND 연산을 통해 블록 사이즈만 가져오겠다.
#define GET_ALLOC(p)    (GET(p) & 0x1)      // 00000001 과 AND 연을 통해 헤더에서 가용여부만 가져오겠다.

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// 가용리스트 명시적 주소 읽기
// prev/next 블록이 가리키는 곳으로 가는 이중포인터 //byte 형식의 주솟값을 가르키는 포인터로 변환해서 바이트 단위로 연산하겠다.
#define PREV_FREE_P(bp) (*(char **)(bp))
#define NEXT_FREE_P(bp) (*(char **)(bp + WSIZE))

// list
static char *heap_listp;            // 힙 포인터
static char *free_listp;            // 가용리스트 첫 위치 포인터

// function prototype
int mm_init(void);
void mm_free(void *bp);
void *mm_malloc(size_t size);
void *mm_realloc(void *bp, size_t size);
static void *extend_heap(size_t words);
static void *find_fit(size_t aszie);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void add_block_to_freelist(void *bp);
static void remove_block(void *bp);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{   
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0);                                     // padding for 2 word 배수
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1));      // prologue header
    PUT(heap_listp + (2 * WSIZE), NULL);                    // previous free block address
    PUT(heap_listp + (3 * WSIZE), NULL);                    // next free block address
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1));      // prologue footer
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));              // epilogue header
    
    free_listp = heap_listp + (2 * WSIZE);
    
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {   
        return -1;
    }

    return 0;
}

/*
 * exxtend_heap 힙을 특정 사이즈만큼 증가. 새 가용 블록 만들기
 */
static void *extend_heap(size_t words)
{   
    char *bp;
    size_t size; 
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    
    bp = mem_sbrk(size);
    if (bp == (void *)-1)
    {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    
    return coalesce(bp);
}


// 가용블록 병합 함수. 앞뒤 가용블럭과 free한 블럭 합치기
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); 
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size =  GET_SIZE(HDRP(bp));

    //이전 블록 과 병합
    if (!prev_alloc) {
        remove_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    //다음 블록과 병합
    if (!next_alloc) {
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    add_block_to_freelist(bp);
    return bp;
}

//가용리스트 추가 함수
static void add_block_to_freelist(void *bp) {
    NEXT_FREE_P(bp) = free_listp;     // Set next to point to the current free list head
    PREV_FREE_P(bp) = NULL;           // Previous is NULL since this will be the new head

    if (free_listp != NULL) {
        PREV_FREE_P(free_listp) = bp; // Update previous head's previous pointer to new block
    }
    
    free_listp = bp;                        // Update the free list head to the new block
}

//block을 free 할때 가용리스트 업데이트
static void remove_block(void *bp) {
    if (PREV_FREE_P(bp)) {
        NEXT_FREE_P(PREV_FREE_P(bp)) = NEXT_FREE_P(bp);
    } else {
        free_listp = NEXT_FREE_P(bp);
    }

    if (NEXT_FREE_P(bp)) {
        PREV_FREE_P(NEXT_FREE_P(bp)) = PREV_FREE_P(bp);
    }
}


/*
 * find fit  // best fit search
 */
static void *find_fit(size_t aszie)
{
    void *bp;
    void *best = NULL;
    for (bp = free_listp; NEXT_FREE_P(bp) != NULL; bp = NEXT_FREE_P(bp))
    {   
        if (aszie == GET_SIZE(HDRP(bp))){
            best = bp;
            return best;
        }
        else if (aszie < GET_SIZE(HDRP(bp)))
        {   
            if (best == NULL || GET_SIZE(best) > GET_SIZE(bp)) {
                best = bp;
            }
        }
    }
    return best;
}

/*
 * place 가용블록에 데이터를 넣고 필요하다면 나머지 부분이 최소 블록크기와 같거나 크면 분할하는 함수
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_block(bp);

    if ((csize - asize) >= (3 * DSIZE))
    {                                          
        PUT(HDRP(bp), PACK(asize, 1));         
        PUT(FTRP(bp), PACK(asize, 1));         
        bp = NEXT_BLKP(bp);                    
        PUT(HDRP(bp), PACK(csize - asize, 0)); 
        PUT(FTRP(bp), PACK(csize - asize, 0)); 

        add_block_to_freelist(bp);              // 가용 리스트 표식
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); 
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    // 어느 시점에 있는 bp를 인자로 받는다.
    size_t size = GET_SIZE(HDRP(bp)); // 얼만큼 free를 해야 하는지.
    PUT(HDRP(bp), PACK(size, 0));     // header, footer 들을 free 시킨다. 안에 들어있는걸 지우는게 아니라 가용상태로 만들어버린다.
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    if (size <= 0)
    {
        mm_free(bp);
        return 0;
    }
    if (bp == NULL)
    {
        return mm_malloc(size);
    }
    void *newp = mm_malloc(size);
    if (newp == NULL)
    {
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if (size < oldsize)
    {
        oldsize = size;
    }
    memcpy(newp, bp, oldsize);
    mm_free(bp);
    return newp;
}
