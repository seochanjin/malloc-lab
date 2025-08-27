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


static void* extend_heap(size_t words);
static void* coalesce(void *bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t asize);


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
static char* *free_listp = NULL;

int mm_init(void)
{
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

    nf_check = heap_listp;
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
    if(size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // 이거 크기가 왜 이러지???
    }

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
    /* 처음부터 NULL이 나와서 다음이 없다. 그런데 왜 돌아간걸까? 효율이 조졌지만 돌아간 흔적이 있다. 좀비 코드
    * 이건 first fit
    *while(GET_SIZE(HDRP(bp))>0){
    *    if(GET_ALLOC(HDRP(bp)) == 1){
    *        return NULL; 
    *    }
    *    if(asize <= GET_SIZE(HDRP(bp))){
    *        return bp;
    *    }
    *    bp = NEXT_BLKP(bp);
    *}
    */
//################################################################################
//     // 이 아래것도 first fit인데 이건 성공한거
//     void* bp = heap_listp;
//     while(GET_SIZE(HDRP(bp)) > 0){
//         if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//             return bp;
//         }

//         bp = NEXT_BLKP(bp);
//     }
//     return NULL;
// //#################################################################################
    // 이건 next_fit
    void* start = nf_check;
    void* bp = start;
    while(GET_SIZE(HDRP(bp)) > 0){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            nf_check = bp;
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }
    for(bp = heap_listp; bp != start; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            nf_check = bp;
            return bp;
        }
    }
    return NULL;
//#################################################################################
    // // 이건 best-fit
    // void* best_bp = NULL; 
    // void* bp = heap_listp;
    // while(GET_SIZE(HDRP(bp)) > 0){
    //     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
    //         if(best_bp == NULL){
    //             best_bp = bp;
    //         }
    //         else{
    //             if(GET_SIZE(HDRP(best_bp)) > GET_SIZE(HDRP(bp))){
    //                 best_bp = bp;
    //             }
    //         }
    //     }
    //     bp = NEXT_BLKP(bp);
    // }
    
    // return best_bp;
    
//#################################################################################

}

static void place(void* bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void* nbp = NEXT_BLKP(bp); // 난 여기까지만 했음. 하고 나서 뒤에걸 어떻게 하지 해버림
        PUT(HDRP(nbp), PACK(csize - asize, 0));
        PUT(FTRP(nbp), PACK(csize - asize, 0));
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
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

static void* coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    void* next_bp = NULL;
    

    if(prev_alloc && next_alloc){
        next_bp = bp;
        return bp;
    }
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        next_bp = bp;
    }
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        next_bp = bp;
    }
    else if(!prev_alloc && !next_alloc){
        size += GET_SIZE(FTRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        next_bp = bp;
    }

    void* start = next_bp;
    void* end = start + GET_SIZE(HDRP(next_bp));

    if(( nf_check >= start) && ( nf_check < end)){
        nf_check = next_bp;
    }
    
    return bp;
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if(ptr == NULL){return mm_malloc(size);} //ptr이 null이면 malloc처럼 동작
    if(size == 0){ //size가 0이면 free 하고 null 반환
        mm_free(ptr);
        return NULL;
    }
    
    size_t old_size = GET_SIZE(HDRP(ptr)); //기존 블록의 총 크기
    
    size_t asize; // 패딩을 합시다~~
    if(size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }


    if(old_size >= asize){ 
        place(ptr, asize);
        return ptr;
    }

    
    void* next = NEXT_BLKP(ptr);
    size_t old_payload = old_size - DSIZE; //기존 블록의 페이로드 크기
    size_t next_alloc = GET_ALLOC(HDRP(next));
    size_t next_size = GET_SIZE(HDRP(next));
    void* prev = PREV_BLKP(ptr);
    size_t prev_alloc = GET_ALLOC(FTRP(prev));
    size_t prev_size = GET_SIZE(HDRP(prev));


    

    // 다음 블록만 free 일때
    if(!next_alloc && (old_size + next_size) >= asize){
        size_t new_size = old_size + next_size;
        PUT(HDRP(ptr), PACK(new_size, 0));
        // PUT(FTRP(ptr), PACK(new_size, 0));
        place(ptr, asize);

        void* merged_start = ptr;
        void* merged_end   = (char*)ptr + new_size;  
        if ((void*)nf_check >= merged_start && (void*)nf_check < merged_end) {
            nf_check = merged_start;
        }

        return ptr;
    }

    //마지막 블록일때
    else if(GET_SIZE(HDRP(next)) == 0 && GET_ALLOC(HDRP(next))){
        size_t need = asize - old_size;
        if(mem_sbrk(need) != (void*)-1){
            size_t new_size = old_size + need;
            PUT(HDRP(ptr), PACK(new_size, 1));
            PUT(FTRP(ptr), PACK(new_size, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
            return ptr;
        }
    }
    

    // 양쪽 블록이 다 free일때
    else if(!prev_alloc && !next_alloc && (prev_size + old_size + next_size) >= asize){
        size_t new_size = prev_size + old_size + next_size;
        void* newptr = prev;
        PUT(HDRP(newptr), PACK(new_size, 0));
        // PUT(FTRP(newptr), PACK(new_size, 0));

        
        memmove(newptr, ptr, old_payload);
        place(newptr, asize);

        // void* merged_start = prev;
        // void* merged_end   = (char*)prev + new_size;       
        // if ((void*)nf_check >= merged_start && (void*)nf_check < merged_end) {
        //     nf_check = merged_start;
        // }

        nf_check = prev;
        return newptr;
    }

    // 전 블록만 free일때
    else if(!prev_alloc && (prev_size + old_size) >= asize){
        size_t new_size = prev_size + old_size;
        void* newptr = prev;
        PUT(HDRP(newptr), PACK(new_size, 0));
        // PUT(FTRP(newptr), PACK(new_size, 0));

        
        memmove(newptr, ptr, old_payload);
        place(newptr, asize);

        // void* merged_start = prev;
        // void* merged_end   = (char*)prev + new_size;     
        // if ((void*)nf_check >= merged_start && (void*)nf_check < merged_end) {
        //     nf_check = merged_start;
        // }

        nf_check = prev;
        return newptr;
    }

    


    //없을때
    void* newptr = mm_malloc(size);
    if(newptr == NULL){return NULL;}
    size_t copy = (old_payload < size) ? old_payload : size;
    memcpy(newptr, ptr, copy);
    mm_free(ptr);
    return newptr;
}

// void *mm_realloc(void *ptr, size_t size)
// {
//     // ptr == NULL -> mm_malloc, size == 0 -> mm_free
//     if (ptr == NULL) {
//         return mm_malloc(size);
//     }
//     if (size == 0) {
//         mm_free(ptr);
//         return NULL;
//     }
//     size_t old_size = GET_SIZE(HDRP(ptr));
//     size_t asize;
//     void *prev_ptr = PREV_BLKP(ptr);
//     void *next_ptr_val = NEXT_BLKP(ptr);
//     int prev_aloc = GET_ALLOC(HDRP(prev_ptr));
//     int next_aloc = GET_ALLOC(HDRP(next_ptr_val));
//     size_t prev_size = GET_SIZE(HDRP(prev_ptr));
//     size_t next_size = GET_SIZE(HDRP(next_ptr_val));
//     size_t total_size;
//     if (size <= DSIZE) {
//         asize = 2 * DSIZE;
//     } else {
//         // 8 배수 올림
//         asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
//     }
//     // 복사할 데이터 크기 계산 -> min(이전 페이로드 크기, 새로 요청된 payload 크기)
//     size_t copySize = old_size - DSIZE;
//     if (size < copySize) {
//         copySize = size;
//     }
//     // case 1: 요청한 크기가 기존 블록 크기와 같다면 바로 리턴
//     if (asize == old_size) {
//         return ptr;
//     }
//     // case 2: 축소하는 경우
//     if (asize < old_size) {
//         // 제자리에서 축소
//         place(ptr, asize);
//         return ptr;
//     }
//     // 확장하는 경우
//     // Case 3.1: 다음 블록이 가용하고 공간이 충분한 경우
//     if (!next_aloc && (asize <= old_size + next_size)) {
//         total_size = old_size + next_size;
//         // 헤더만 전체 크기로 미리 설정하고 place 호출
//         PUT(HDRP(ptr), PACK(total_size, 0));
//         place(ptr, asize);
//         return ptr;
//     }
    
//     // Case 3.3: 앞, 뒤 블록 모두 가용하고 공간이 충분한 경우
//     else if (!prev_aloc && !next_aloc && (asize <= old_size + prev_size + next_size)) {
//         total_size = old_size + prev_size + next_size;
//         memmove(prev_ptr, ptr, copySize);
//         // 헤더만 전체 크기로 미리 설정하고 place 호출
//         PUT(HDRP(prev_ptr), PACK(total_size, 0));
//         place(prev_ptr, asize);
//         nf_check = prev_ptr;
//         return prev_ptr;
//     }
//     // Case 3.4: 앞 블록만 가용하고 공간이 충분한 경우
//     else if (!prev_aloc && (asize <= old_size + prev_size)) {
//         total_size = old_size + prev_size;
//         memmove(prev_ptr, ptr, copySize);
//         // 헤더만 전체 크기로 미리 설정하고 place 호출
//         PUT(HDRP(prev_ptr), PACK(total_size, 0));
//         place(prev_ptr, asize);
//         nf_check = prev_ptr;
//         return prev_ptr;
//     }
//     // Case 3.2: 다음 블록이 힙의 끝(에필로그)인 경우
//     else if (next_size == 0) {
//         // 필요한 추가 공간 계산
//         size_t needsize = asize - old_size;
//         // mem_sbrk로 필요한 만큼만 할당
//         if (mem_sbrk(needsize) == (void *)-1) {
//             return NULL;
//         }
//         // 현재 블럭의 헤더, 푸터 설정
//         PUT(HDRP(ptr), PACK(asize, 1));
//         PUT(FTRP(ptr), PACK(asize, 1));
//         // 새 에필로그 설정
//         PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
//         return ptr;
//     }
//     // Case 4: 위 모든 방법으로 확장 불가, 새로 할당
//     else {
//         void *new_ptr = mm_malloc(size);
//         if (new_ptr == NULL) {
//             return NULL;
//         }
//         memcpy(new_ptr, ptr, copySize);
//         mm_free(ptr);
//         return new_ptr;
//     }
// }

