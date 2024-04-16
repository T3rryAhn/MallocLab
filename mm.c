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

#define WSIZE 4             // word size (bytes)
#define DSIZE 8             // double word size (bytes)
#define CHUNKSIZE (1 << 12) // increase heap size to 4KB (4096 bytes) 메모리 페이지 크기가 4KB

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc)) // size + block available. OR 연산으로 헤더에 넣을 정보를 만듬 사이즈 + 가용여부(끝 3자리)

// Read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (int)(val))

// Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7) // 00000111 의 보수(~) 를 취해서 11111000 을 가져와 AND 연산을 통해 블록 사이즈만 가져오겠다.
#define GET_ALLOC(p) (GET(p) & 0x1) // 00000001 과 AND 연산을 통해 헤더에서 가용여부만 가져오겠다.

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// 가용 리스트 이동
#define NEXT_FREE_PTR(bp)    (*(char **)(bp + WSIZE))
#define PREV_FREE_PTR(bp)    (*(char **)(bp))


static char *heap_listp; // 처음에 쓸 큰 가용블록 힙을 만들어줌.
static char *free_listp; // 가용 리스트.

// prototype
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);



// mm_init - initialize the malloc package.
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), NULL);
    PUT(heap_listp + (3 * WSIZE), NULL);
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1));
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));

    free_listp = heap_listp + (2 * WSIZE);                 

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    { // extend heap을 통해, 시작할 때 한번 heap을 늘려줌. 늘리는 양은 상관없음.
        return -1;
    }
    return 0;
}


// exxtend_heap 힙을 특정 사이즈만큼 증가
static void *extend_heap(size_t words)
{ 
    char *bp;
    size_t size; 
    
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;       // double word 정렬. 즉 8 바이트 정렬.

    if (bp = mem_sbrk(size) == (void *)-1) // 0xffffffff
    {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));                   // blk header
    PUT(FTRP(bp), PACK(size, 0));                   // blk footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));           // epilogue header

    return coalesce(bp);
} 


// 블록을 연결하는 함수
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size =  GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){                                      // case 1 - 이전과 다음 블록이 모두 할당 되어있는 경우, 현재 블록의 상태는 할당에서 가용으로 변경
        return bp;                                                      // 이미 free에서 가용이 되어있으니 여기선 따로 free 할 필요 없음.
    }
    else if (prev_alloc && !next_alloc){                                // case2 - 이전 블록은 할당 상태, 다음 블록은 가용상태. 현재 블록은 다음 블록과 통합 됨.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));                          // 다음 블록의 헤더를 보고 그 블록의 크기만큼 지금 블록의 사이즈에 추가한다.
        PUT(HDRP(bp),PACK(size,0));                                     // 헤더 갱신(더 큰 크기로 PUT)
        PUT(FTRP(bp), PACK(size,0));                                    // 푸터 갱신
    }
    else if(!prev_alloc && next_alloc){                                 // case 3 - 이전 블록은 가용상태, 다음 블록은 할당 상태. 이전 블록은 현재 블록과 통합. 
        size+= GET_SIZE(HDRP(PREV_BLKP(bp))); 
        PUT(FTRP(bp), PACK(size,0));                                    // 푸터에 먼저 조정하려는 크기로 상태 변경한다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));                         // 현재 헤더에서 그 앞블록의 헤더 위치로 이동한 다음에, 조정한 size를 넣는다.
        bp = PREV_BLKP(bp);                                             // bp를 그 앞블록의 헤더로 이동(늘린 블록의 헤더이니까.)
    }
    else {                                                              // case 4- 이전 블록과 다음 블록 모두 가용상태. 이전,현재,다음 3개의 블록 모두 하나의 가용 블록으로 통합.
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 헤더, 다음 블록 푸터 까지로 사이즈 늘리기
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));                         // 헤더부터 앞으로 가서 사이즈 넣고
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));                         // 푸터를 뒤로 가서 사이즈 넣는다.
        PUT(PREV_FREE(PREV_BLKP(bp)),PREV_FREE_PTR(bp));

        bp = PREV_BLKP(bp);                                             // 헤더는 그 전 블록으로 이동.
    }
    return bp;
}






// find fit  first fit search

static void *find_fit(size_t aszie)
{
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (aszie <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    return NULL;
}


// place
static void place(void *bp, size_t asize)
{ // 들어갈 위치를 포인터로 받는다.(find fit에서 찾는 bp) 크기는 asize로 받음.
    // 요청한 블록을 가용 블록의 시작 부분에 배치, 나머지 부분의 크기가 최소 블록크기와 같거나 큰 경우에만 분할하는 함수.
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 있는 블록의 사이즈.
    if ((csize - asize) >= (2 * DSIZE))
    {                                          // 현재 블록 사이즈안에서 asize를 넣어도 2*DSIZE(헤더와 푸터를 감안한 최소 사이즈)만큼 남냐? 남으면 다른 data를 넣을 수 있으니까.
        PUT(HDRP(bp), PACK(asize, 1));         // 헤더위치에 asize만큼 넣고 1(alloc)로 상태변환. 원래 헤더 사이즈에서 지금 넣으려고 하는 사이즈(asize)로 갱신.(자르는 효과)
        PUT(FTRP(bp), PACK(asize, 1));         // 푸터 위치도 변경.
        bp = NEXT_BLKP(bp);                    // regular block만큼 하나 이동해서 bp 위치 갱신.
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 나머지 블록은(csize-asize) 다 가용하다(0)하다라는걸 다음 헤더에 표시.
        PUT(FTRP(bp), PACK(csize - asize, 0)); // 푸터에도 표시.
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 위의 조건이 아니면 asize만 csize에 들어갈 수 있으니까 내가 다 먹는다.
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
