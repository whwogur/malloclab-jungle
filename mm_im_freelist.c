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
    "SWJUNGLE",
    /* First member's full name */
    "whwogur",
    /* First member's email address */
    "cjh",
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
/* Basic constants and macros */
#define WSIZE 4 // Word and header/footer size(bytes)
#define DSIZE 8 // Double word size (bytes)
#define CHUNKSIZE (1<<12) // Extend heap by this size

#define MAX(x, y) ((x) > (y)? (x) : (y))
// pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))
// Read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// Read the size and allocated fields from address
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// global vars
static void *heap_listp; // heap's start point
static void *prev_listp; // next_fit start point

static void *extend_heap(size_t);
static void *coalesce(void*);
static void *find_fit(size_t asize);
// static void *next_fit(size_t allo_size);
static void place(void *bp, size_t asize);
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // Create initial empty heap
    heap_listp = mem_sbrk(4*WSIZE);
    if (heap_listp == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // allocate an even number of words to maintain alignment
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    // initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0)); // free block header
    PUT(FTRP(bp), PACK(size, 0)); // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // new epilogue header

    // coalesce if the previous block was free
    return coalesce(bp);
}

void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void *find_fit(size_t asize)
{
    // First fit search
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            // prev_listp = bp;
            return bp;
        }
    }
    return NULL; // no fit
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; // adjusted block size
    size_t extendsize; // amount to extend heap if no fit
    char *bp;

    // ignore spurious requests
    if (size == 0)
        return NULL;
    
    // adjust block size to include overhead and alignment reqs
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    // Search the free list for a fit
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    // no fit found, get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
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
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) { // case 1
        return bp;
    }

    else if (prev_alloc && !next_alloc) { // case 2
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

    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{ // 요청 사이즈가 기존 사이즈보다 작으면 요청 사이즈만큼의 데이터만 잘라서 옮긴다.
    if (size == 0) {
        mm_free(ptr);
        return 0;
    }

    if (ptr == NULL)
    return mm_malloc(size);

    void *newp = mm_malloc(size);
    if (newp == NULL)
        return 0;
    
    size_t copySize = GET_SIZE(HDRP(ptr));

    if (size < copySize)
        copySize = size;
    
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}