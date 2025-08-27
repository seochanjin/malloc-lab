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

// 가용 리스트 조작을 위한 기본 상수 및 매크로
#define WSIZE 4 // Word and header/footer size(bytes)
#define DSIZE 8 // Double word size(bytes)
#define CHUNKSIZE (1<<12) // Extend heap by this amjount(bytes)

#define MAX(x, y) ((x)>(y)?(x):(y))

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p
#define GET(p) (*(unsigned int*)(p))
#define PUT(p, val) (*(unsigned int*)(p) = (val))

// Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))

//명시적을 위한 매크로 생성
#define PTRSIZE ((size_t)sizeof(void*))
#define PRED(bp) (*(void **)(bp)) //free 블록의 prev 포인터
#define SUCC(bp) (*(void **)((char*)(bp) + PTRSIZE)) //free 블록의 next 포인터
#define MINBLK ALIGN((size_t)WSIZE + PTRSIZE + PTRSIZE + (size_t)WSIZE) // 64-bit면 24B, 32-bit면 16B. ALIGN로 8바이트 정렬 보장


static void* extend_heap(size_t words);
static void* coalesce(void *bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t asize);
static void insert_node(void *bp);
static void remove_node(void *bp);

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

/*
 * mm_init - initialize the malloc package.
 */
static char* heap_listp = NULL;
static char* nf_check = NULL;
static void* free_listp = NULL; //free list의 시작 주소(root)

int mm_init(void)
{
    //명시적 가용 리스트 헤드를 매번 초기화
    free_listp = NULL;

    if((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1){
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }

    // nf_check = heap_listp;
    return 0;
}

static void* extend_heap(size_t words){
    
    size_t size = (words & 1) ? (words+1)*WSIZE : words*WSIZE;
    char* bp = mem_sbrk(size);

    if (bp == (void*)-1) {return NULL;}
    
    // 시작 새로운 블록 헤더/풋터 그리고 에필로그 헤더
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; // 블록 사이즈 정의
    size_t extendsize; // 사이즈가 맞지 않을 경우 확장해야 하는 핏의 크기?
    char *bp;

    // 사이즈 0으로 부르는 헛짓 컷
    if(size == 0) {return NULL;}

    // 오버헤드와 정렬 reqs? 포함하는 블럭 사이즈 정의
    
    asize = ALIGN(size + 2*WSIZE); //헤더 + 풋터 포함 정렬
    if (asize < MINBLK) asize = MINBLK; // * free 블록이 되어도 preed/succ 수납 가능

    // 크기를 만족하는 프리 리스트를 찾기
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    // 크기를 만족하는 것을 발견하지 못했을 때 메모리를 더 받고 블록은 위치한다
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}

// 꼭 맞는 것을 찾는다? 아니지 이건 asize보다 크기만 하면 바로 거기다 할당하는거지
static void* find_fit(size_t asize){
//################################################################################
    // //first fit
    // void* bp;
    // for(bp = free_listp; bp != NULL; bp = SUCC(bp)){
    //     if(asize <= GET_SIZE(HDRP(bp))){
    //         return bp;
    //     }
    // }
    // return NULL;
//#################################################################################
    // // 이건 next_fit
    // void* start = nf_check;
    // void* bp = start;
    // while(GET_SIZE(HDRP(bp)) > 0){
    //     if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
    //         nf_check = bp;
    //         return bp;
    //     }
    //     bp = NEXT_BLKP(bp);
    // }
    // for(bp = heap_listp; bp != start; bp = NEXT_BLKP(bp)){
    //     if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
    //         nf_check = bp;
    //         return bp;
    //     }
    // }
    // return NULL;
//#################################################################################
     // best-fit
    void* bp = free_listp;
    void* best = NULL;
    size_t bestsz = (size_t)-1;
    int scanned = 0;
    int budget = 64;

    for(; bp && scanned < budget; bp = SUCC(bp), ++scanned){
        size_t sz = GET_SIZE(HDRP(bp));
        if(sz >= asize){
            if(sz == asize) return bp;
            if(sz < bestsz) {best = bp; bestsz = sz;}
        }
    }
    return best;
    
//#################################################################################
}

static void place(void* bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    remove_node(bp);

    if((csize - asize) >= MINBLK){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void* nbp = NEXT_BLKP(bp);
        PUT(HDRP(nbp), PACK(csize-asize, 0));
        PUT(FTRP(nbp), PACK(csize-asize, 0));
        insert_node(nbp);
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void mm_free(void* bp){
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    bp = coalesce(bp);
}

//현재는 first를 기준으로 해보도록 하자~
static void* coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // Case 1: 이전, 다음 블록 모두 할당 상태 (병합 없음)
    if (prev_alloc && next_alloc) {
        insert_node(bp);
        return bp;
    }

    // Case 2: 다음 블록만 가용 상태
    else if (prev_alloc && !next_alloc) {
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        insert_node(bp);
        return bp;
    }

    // Case 3: 이전 블록만 가용 상태
    else if (!prev_alloc && next_alloc) {
        remove_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0)); // 중요: bp의 풋터를 먼저 업데이트
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        insert_node(bp);
        return bp;
    }

    // Case 4: 이전, 다음 블록 모두 가용 상태
    else {
        remove_node(PREV_BLKP(bp));
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 맨 끝 풋터 업데이트
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0)); // 맨 앞 헤더 업데이트
        insert_node(bp);
        return bp;
    }
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if(ptr == NULL) return mm_malloc(size);
    if(size == 0){
        mm_free(ptr);
        return NULL;
    }

    //정렬 포함 실제 필요한 블록 크기(asize) 계산
    size_t asize = ALIGN(size + 2*WSIZE);
    if(asize < MINBLK) asize = MINBLK;

    size_t old_size = GET_SIZE(HDRP(ptr)); //전체 블록 크기(헤더 + 풋터 포함)
    size_t old_payload = old_size - DSIZE; //페이로드 크기

    if(old_size >= asize){
        size_t rem = old_size - asize;
        if(rem >= MINBLK){
            //앞쪽은 할당 블록(asize)
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));

            //뒤쪽은 새 free 블록(rem) -> coalesce가 free list에 너어줌
            void* nbp = NEXT_BLKP(ptr);
            PUT(HDRP(nbp), PACK(rem, 0));
            PUT(FTRP(nbp), PACK(rem, 0));
            coalesce(nbp);
        }
        //남는 공간이 너무 작으면 그냥 그대로 둠
        return ptr;
    }

    // next 가용 블록 흡수해서 확장
    void* next = NEXT_BLKP(ptr);
    size_t next_alloc = GET_ALLOC(HDRP(next));
    size_t next_size = GET_SIZE(HDRP(next));

    if(!next_alloc && (old_size + next_size) >= asize){
        //next는 free list안에 있으므로 먼저 제거
        remove_node(next);

        size_t new_size = old_size + next_size;
        size_t rem = new_size - asize;

        if (rem >= MINBLK){
            //앞쪽을 asize로 고정하고 꼬리를 free로 만듦
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));

            void* nbp = NEXT_BLKP(ptr);
            PUT(HDRP(nbp), PACK(rem, 0));
            PUT(FTRP(nbp), PACK(rem, 0));
            coalesce(nbp);
        }
        else{
            //전부 할당
            PUT(HDRP(ptr), PACK(new_size, 1));
            PUT(FTRP(ptr), PACK(new_size, 1));
        }
        return ptr;
    }

    // prev 가용 블록 흡수해서 확장 (데이터 이동 필요)
    void* prev = PREV_BLKP(ptr);
    size_t prev_alloc = GET_ALLOC(FTRP(prev));
    size_t prev_size = GET_SIZE(HDRP(prev));

    if (!prev_alloc && (prev_size + old_size) >= asize) {
        remove_node(prev);

        void *newptr  = prev;
        size_t new_size = prev_size + old_size;
        size_t rem = new_size - asize;

        // 먼저 안전하게 데이터 이동
        memmove(newptr, ptr, old_payload);

        if (rem >= MINBLK) {
            PUT(HDRP(newptr), PACK(asize, 1));
            PUT(FTRP(newptr), PACK(asize, 1));

            void *nbp = NEXT_BLKP(newptr);
            PUT(HDRP(nbp), PACK(rem, 0));
            PUT(FTRP(nbp), PACK(rem, 0));
            coalesce(nbp);
        } else {
            PUT(HDRP(newptr), PACK(new_size, 1));
            PUT(FTRP(newptr), PACK(new_size, 1));
        }
        return newptr;
    }

    // prev + next 모두 가용이면 둘 다 흡수
    if (!prev_alloc && !next_alloc && (prev_size + old_size + next_size) >= asize) {
        remove_node(prev);
        remove_node(next);

        void *newptr = prev;
        size_t new_size = prev_size + old_size + next_size;
        size_t rem = new_size - asize;

        memmove(newptr, ptr, old_payload);

        if (rem >= MINBLK) {
            PUT(HDRP(newptr), PACK(asize, 1));
            PUT(FTRP(newptr), PACK(asize, 1));

            void *nbp = NEXT_BLKP(newptr);
            PUT(HDRP(nbp), PACK(rem, 0));
            PUT(FTRP(nbp), PACK(rem, 0));
            coalesce(nbp);
        } else {
            PUT(HDRP(newptr), PACK(new_size, 1));
            PUT(FTRP(newptr), PACK(new_size, 1));
        }
        return newptr;
    }
    // 마지막에 있을 경우
    if (GET_SIZE(HDRP(next)) == 0 && GET_ALLOC(HDRP(next))) {
        size_t need = asize - old_size;
        if (mem_sbrk(need) != (void *)-1) {
            size_t new_size = old_size + need;
            PUT(HDRP(ptr), PACK(new_size, 1));
            PUT(FTRP(ptr), PACK(new_size, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); // 새 에필로그
            return ptr;
        }
    }
    // 새로 할당해서 복사
    void *newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;

    size_t copy = (old_payload < size) ? old_payload : size;
    memcpy(newptr, ptr, copy);
    mm_free(ptr);
    return newptr;

}


// void *mm_realloc(void *ptr, size_t size) {
//     if (ptr == NULL) return mm_malloc(size);
//     if (size == 0) { mm_free(ptr); return NULL; }

//     void *newptr = mm_malloc(size);
//     if (!newptr) return NULL;

//     size_t old_payload = GET_SIZE(HDRP(ptr)) - DSIZE;
//     size_t copy = old_payload < size ? old_payload : size;
//     memcpy(newptr, ptr, copy);
//     mm_free(ptr);
//     return newptr;
// }

//삽입 함수: 새 블록을 free list 앞에 붙이는 방식
static void insert_node(void* bp){
    SUCC(bp) = free_listp;
    PRED(bp) = NULL;
    if(free_listp != NULL){
        PRED(free_listp) = bp;
    }
    free_listp = bp;
}

//제거 함수: 할당되거나 병합될 때 free list에서 빼는 방식
static void remove_node(void* bp){
    void* prev = PRED(bp);
    void* next = SUCC(bp);
    if(prev) {SUCC(prev) = next;} else {free_listp = next;}
    if(next) {PRED(next) = prev;} 
}