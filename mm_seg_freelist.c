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
    "whwogur",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/* 기본 단위인 word, double word, 새로 할당받는 메모리 크기 CHUNKSIZE를 정의한다 */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define MINIMUM     8       /* Initial Prologue block size, header, footer, PREC, SUCC */
#define CHUNKSIZE   (1<<12) /* Extend heap by this amount : 4096bytes -> 4kib */
#define LISTLIMIT 20

#define MAX(x, y) ((x) > (y) ? (x) : (y))  // 최댓값 구하는 함수 매크로

/* header 및 footer 값(size + allocated) 리턴 */
#define PACK(size, alloc)   ((size) | (alloc))   

/* 주소 p에서의 word를 읽어오거나 쓰는 함수 */
#define GET(p)          (*(unsigned int*)(p))
#define PUT(p, val)     (*(unsigned int*)(p) = (val))

/* header or footer에서 블록의 size, allocated field를 읽어온다 */
#define GET_SIZE(p)     (GET(p) & ~0x7) // ~0x00000111 -> 0x11111000
#define GET_ALLOC(p)    (GET(p) & 0x1)    

/* 블록 포인터 bp를 인자로 받아 블록의 header와 footer의 주소를 반환한다 */
#define HDRP(bp)    ((char*)(bp) - WSIZE) 
#define FTRP(bp)    ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)// 헤더 + 데이터 + 푸터 - (헤더 + 푸터)

/* 블록 포인터 bp를 인자로 받아 이후, 이전 블록의 주소를 리턴한다 */
// 현재 bp에서 WSIZE를 빼서 header로감 -> header에서 GETSIZE
// -> 현재 블록 크기 return받음(헤더+데이터+푸터) -> 그걸 bp에 더하면 nextbp
#define NEXT_BLKP(bp)   ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) // (char*)(bp) + GET_SIZE(지금 블록의 헤더값)
#define PREV_BLKP(bp)   ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // (char*)(bp) - GET_SIZE(이전 블록의 풋터값)

/* free list 상에서의 이전, 이후 블록의 포인터를 리턴한다. */
#define PREC_FREEP(bp)  (*(void**)(bp))             // 이전 블록의 bp
#define SUCC_FREEP(bp)  (*(void**)(bp + WSIZE))     // 이후 블록의 bp

static char* heap_listp;
// static char* free_listp = NULL; // free list의 맨 첫 블록을 가리키는 포인터
static void* seg_list[LISTLIMIT];

static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t newsize);

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);
// 이니셜라이징
int mm_init(void) {
    for (int i = 0; i < LISTLIMIT; i++) {
        seg_list[i] = NULL;
    }
    /* padding, prol_header, prol_footer, PREC, SUCC, epil_header */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void*)-1) return -1;

    PUT(heap_listp, 0);  // Alignment padding. 더블 워드 경계로 정렬된 미사용 패딩.
    PUT(heap_listp + (1 * WSIZE), PACK(MINIMUM, 1));  // prologue header 8/1
    PUT(heap_listp + (2 * WSIZE), PACK(MINIMUM, 1));  // prologue footer 8/1
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));      // epliogue header 0/1
    heap_listp = heap_listp + 2*WSIZE;
    /* 그 후 CHUNKSIZE만큼 힙을 확장해 초기 가용 블록을 생성한다. */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1; // 실패하면 -1 리턴
    }
    return 0;
}

// extend_heap : 워드 단위 메모리를 인자로 받아 힙을 늘려준다.
static void* extend_heap(size_t words){ // 워드 단위로 받는다.
    char* bp;
    size_t size;
    
    /* mem_sbrk 함수를 이용해 할당받는다. */
    size = (words % 2) ? (words + 1) * WSIZE : (words) * WSIZE; // size를 짝수 word & byte 형태로 만든다.
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    } /* mem_brk는 heap의 첫 주소, mem_sbrk 함수는 그 주소값을 기억하기 위해 임시변수 old_brk를 만들어주고
    전역변수인 mem_brk를 늘려주고 리턴은 old_brk를 반환 */
    
    PUT(HDRP(bp), PACK(size, 0)); // 가용 블록 header 만들기
    PUT(FTRP(bp), PACK(size, 0)); // 가용 블록 footer 만들기
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // 에필로그 헤더 위치 변경

    return coalesce(bp);
}
void *mm_malloc(size_t size) {
    int asize = ALIGN(size + SIZE_T_SIZE);
    size_t extendsize;
    char* bp;

    // fit에 맞는 free리스트 찾기
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize); // 필요하다면 분할하여 할당한다.
        return bp;
    }

    // 만약 맞는 크기의 가용 블록이 없다면 새로 힙을 늘려서 새 힙에 메모리를 할당한다.
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    } 
    place(bp, asize);
    return bp;
}
// coalesce(bp) : 해당 가용 블록을 앞뒤 가용 블록과 연결하고 연결된 가용 블록의 주소를 리턴한다.
static void* coalesce(void* bp) {
    // 직전 블록의 footer, 직후 블록의 header를 보고 가용 여부를 확인.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 직전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 직후 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp)); // 현재 사이즈

    // case 1 : 직전, 직후 블록이 모두 할당 -> 해당 블록만 free list에 넣어주면 된다.
    if (prev_alloc && next_alloc) {
        putFreeBlock(bp,size);
        return bp;
    }
    // case 2 : 직전 블록 할당, 직후 블록 가용
    else if (prev_alloc && !next_alloc) {
        removeBlock(NEXT_BLKP(bp));    // free 상태였던 직후 블록을 free list에서 제거한다.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) { // case 3 : prev block not allocated, next block allocated
        removeBlock(PREV_BLKP(bp));    // 직전 블록을 free list에서 제거하고 합쳐서 insert
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        PUT(FTRP(bp), PACK(size, 0));  
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp); 
    }
    else if (!prev_alloc && !next_alloc) { // case 4 : prev, next both not allocated
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));  
        bp = PREV_BLKP(bp);
    }
    
    // 연결된 새 가용 블록을 free list에 추가한다.
    putFreeBlock(bp, size);
    return bp;
}
// first_fit : 힙의 맨 처음부터 탐색하여 요구하는 메모리 공간보다 큰 가용 블록의 주소를 반환한다.
static void* find_fit(size_t asize){
    /* First-fit */
    void* bp;
    int list = 0;
    size_t searchsize = asize;
    
    while (list < LISTLIMIT) {
        /* list(0~19) 가용블록을 못찾고 19번째 리스트에 도달하거나, 나보다 큰 사이즈의
        seg_list가 NULL이 아니면 */
        if ((list == LISTLIMIT-1) || (searchsize <= 1) && (seg_list[list] != NULL)) {
            bp = seg_list[list];
            while ((bp != NULL) && (asize > GET_SIZE(HDRP(bp)))) {
                bp = SUCC_FREEP(bp);
            }
            if (bp != NULL) {
                return bp;
            }
        }
        searchsize >>= 1;
        list++;
    }
    // no fit
    return NULL;
}
// place(bp, size): 요구 메모리를 할당할 수 있는 가용 블록을 할당한다. 이 때 분할이 가능하면 분할한다.
static void place(void* bp, size_t asize){
    // 현재 할당할 수 있는 후보 가용 블록의 주소
    size_t csize = GET_SIZE(HDRP(bp));

    // 할당될 블록이므로 free list에서 없애준다.
    removeBlock(bp);
    // 필요한 블록 빼고 남는게 16바이트 이상이면
    if ((csize - asize) >= (2*DSIZE)) {
        // 할당처리
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);// bp를 다음블록으로
        // 나머지 사이즈 free처리
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);
        // 이때 연결돼있는게 있을 수 있으므로 coalesce
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
// 오름차순으로 정렬된 seq list에서 크기에 맞게 탐색하여 삽입
void putFreeBlock(void* bp, size_t size) { 
    int idx = 0;
    void *search_ptr;
    void *insert_ptr = NULL; // searchptr의 값을 저장해놓는 용도

    while ((idx < LISTLIMIT - 1) && (size > 1)) { //seg_list idx 탐색
        size >>= 1;
        idx++;
    }

    search_ptr = seg_list[idx];
    // 넘겨받은 사이즈 보다 큰 사이즈 나올때까지 탐색
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = SUCC_FREEP(search_ptr);
    }

    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            SUCC_FREEP(bp) = search_ptr;
            PREC_FREEP(bp) = insert_ptr;
            PREC_FREEP(search_ptr) = bp;
            SUCC_FREEP(insert_ptr) = bp;
        } else {
            SUCC_FREEP(bp) = search_ptr;
            PREC_FREEP(bp) = NULL;
            PREC_FREEP(search_ptr) = bp;
            seg_list[idx] = bp;
        }
    } else {
        if (insert_ptr != NULL) {
            SUCC_FREEP(bp) = NULL;
            PREC_FREEP(bp) = insert_ptr;
            SUCC_FREEP(insert_ptr) = bp;
        } else { // list에 처음 삽입
            SUCC_FREEP(bp) = NULL;
            PREC_FREEP(bp) = NULL;
            seg_list[idx] = bp;
        }
    }
    return;
}
// removeBlock(bp) : 할당되거나 연결되는 가용 블록을 free list에서 없앤다.
void removeBlock(void *bp) {
    int idx = 0;
    size_t size = GET_SIZE(HDRP(bp));

    while ((idx < LISTLIMIT - 1) && (size > 1)) { // 지우려는 list idx 탐색
        size >>= 1;
        idx++;
    }

    if (SUCC_FREEP(bp) != NULL) { // successor != NULL이면
        if (PREC_FREEP(bp) != NULL) { // predecessor != NULL 중간에있는걸 지우는경우
            PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
            SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        } else { // pred 블록이 NULL일 경우
            PREC_FREEP(SUCC_FREEP(bp)) = NULL;
            seg_list[idx] = SUCC_FREEP(bp);
        }
    } else { // successor == NULL
        if (PREC_FREEP(bp) != NULL) { // 리스트 맨 끝 블록인 경우
            SUCC_FREEP(PREC_FREEP(bp)) = NULL;
        } else { // 하나만 있었을 경우
            seg_list[idx] = NULL;
        }
    }
    return;
}
// free되면 가용블록끼리 합쳐주고 header, footer 갱신
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0)); // 헤더 갱신
    PUT(FTRP(bp), PACK(size, 0)); // 푸터 갱신
    coalesce(bp); // 합치기
}
// realloc은 malloc으로 새로 할당하고 그 전에 있는 것은 free해줌
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize); // oldptr로부터 copySize만큼 깊은복사
    mm_free(oldptr);
    return newptr;
}