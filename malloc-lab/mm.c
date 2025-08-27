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

#define NUM_BINS 20


static void* extend_heap(size_t words);
static void* coalesce(void *bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t asize);
static void insert_node(void *bp);
static void remove_node(void *bp);
static inline int bin_index(size_t asize);

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
//8로 나눴을때 나머지가 있으면 다음 배수로 올리기 위해 여유를 더해준다. ex) size = 10 -> 10 + 7 = 17
//결과값의 하위 3비트를 날려서 8의 배수로 만든다. ex) 17 & 0xFFFFFFF8 = 16
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
 * mm_init - initialize the malloc package.
 */
static char* heap_listp = NULL;
static void* bins[NUM_BINS];


int mm_init(void)
{   //분리 맞춤을 하기 위한 20개의 가용 리스트 시작점을 모두 NULL로 초기화
    for(int i = 0; i < NUM_BINS; i++){ 
        bins[i] = NULL;
    }

    //힙의 앞부분에 경계 확인을 위한 프롤로그와 에필로그 블록을 만들 공간 16바이트를 확보
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1){
        return -1;
    }

    // 위에서 말한 프롤로그와 에필로그 값을 기록
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);

    //초기 힙 공간을 CHUNKSIZE 만큼 확보하여 첫 번째 가용 블록을 만든다.
    // if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
    //     return -1;
    // }

    return 0;
}

static void* extend_heap(size_t words){
    //요청된 words가 홀수일 경우 짝수로 만들어 mem_sbrk로 요청할 전제 size가 항상 8의 배수가 되도록 보장
    size_t size = (words & 1) ? (words+1)*WSIZE : words*WSIZE;

    //mem_sbrk를 호출하여 실제로 힙의 크기를 늘리고 시스템 메모리가 부족하여 확장에 실패할 경우 NULL을 반환해 오류를 처리 
    char* bp = mem_sbrk(size);
    if (bp == (void*)-1){
        return NULL;
    }
    
    //새로 확보한 메모리 공간에 헤더와 푸터를 설정하여 유효한 가용 블록으로 만든다.
    //동시에 확장된 힙의 새로운 끝을 표시하기 위해 새로운 에필로그 헤더를 설치
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    //힙을 확장하기 직전에 마지막 블록이 가용 상태였을 수도 있다.
    //이 경우 방금 새로 만든 가용 블록과 이전의 가용 블록이 맞닿게 된다.
    //coalesce(bp)를 호출하여 이 두 블록을 하나의 더 큰 가용 블록으로 병합해야 한다.
    return coalesce(bp);
}


void *mm_malloc(size_t size)
{
    size_t asize; // 블록 사이즈 정의
    size_t extendsize; // 사이즈가 맞지 않을 경우 확장해야 하는 핏의 크기?
    char *bp;

    // 사이즈 0으로 부르는 헛짓 컷
    if(size == 0) {return NULL;}

    //사용자가 10바이트를 요청하더라도 헤더/푸터(8바이트)를 포함하고 8바이트 정렬 규칙을 따라야 하므로 더 큰 공간이 필요하다
    asize = ALIGN(size + 2*WSIZE); //헤더 + 풋터 포함시켜서 8의 배수로 만들어준다.
    if (asize < 2*DSIZE) asize = 2*DSIZE; // * free 블록이 되어도 preed/succ 수납 가능(최소 크기)

    // find_fit을 호출하여 bins에 저장된 가용 블록 리스트들 중에서 asize를 담을 수 있는 블록이 있는지 찾아본다.
    if ((bp = find_fit(asize)) != NULL){ //있을 경우
        place(bp, asize); //place 함수를 통해 할당 상태로 변경
        return bp; //사용자에게 포인터 반납
    }

    // find_fit이 실패했을 경우 재활용할 공간이 없으니 OS로부터 새 메모리를 받아온다.
    extendsize = MAX(asize, CHUNKSIZE); // 16바이트가 필요하다고 해서 16바이트만 받는게 아니라 최소 CHUNKSIZE만큼 넉넉하게 받아온다.
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}
//####################################################################################################################################
//best_fit
static void* find_fit(size_t asize){
    // bin_index를 통해 요청된 크기가 들어갈 만한 가장 작은 bin의 번호를 알아낸다.
    int i = bin_index(asize);
    //best는 최종적으로 선택될 최적의 블록을 저장할 포인터
    void* best = NULL; 
    //bestsz는 지금까지 찾은 최적 블록의 크기를 저장.
    //(size_t)-1은 부호없는 정수에서 가장 큰 값, 어떤 블록이든 처음에는 이것보다 작아서 best 부호가 될 수 있다.
    size_t bestsz = (size_t)-1; 
    for (int b = i; b < NUM_BINS; b++) { //시작점 i부터 모든 bin을 확인
        for (void* bp = bins[b]; bp ; bp = SUCC(bp)) { //각 bin 안의 가용 블록을 모두 확인
            size_t sz = GET_SIZE(HDRP(bp));
            if (sz >= asize) {
                if (sz == asize){
                    return bp;
                }
                if(sz < bestsz){
                    best = bp;
                    bestsz = sz;
                }
            }
        }
    }
    return best;
}
//####################################################################################################################################
// //first_fit
// static void* find_fit(size_t asize){
//     // bin_index를 통해 요청된 크기가 들어갈 만한 가장 작은 bin의 번호를 알아낸다.
//     int i = bin_index(asize);
//     for (int b = i; b < NUM_BINS; b++) { //시작점 i부터 모든 bin을 확인
//         for (void* bp = bins[b]; bp ; bp = SUCC(bp)) { //각 bin 안의 가용 블록을 모두 확인
//             size_t sz = GET_SIZE(HDRP(bp));
//             if (sz >= asize) {
//                 return bp;
//             }
//         }
//     }
    
//     return NULL;
// }
//####################################################################################################################################

//할당
static void place(void* bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    remove_node(bp);

    size_t rem = csize - asize;

    // 스플린터만 방지: 너무 작은 꼬리만 아니면 쪼개기
    // (MINBLK + DSIZE 정도 여유를 요구해 작은 조각 양산을 막음)
    if (rem >= (MINBLK)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(rem, 0));
        PUT(FTRP(bp), PACK(rem, 0));
        insert_node(bp);
    } else {
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

        //앞쪽은 할당 블록(asize)
        PUT(HDRP(ptr), PACK(old_size, 1));
        PUT(FTRP(ptr), PACK(old_size, 1));
        
        return ptr;
    }

    // next 가용 블록 흡수해서 확장
    void* next = NEXT_BLKP(ptr);
    size_t next_alloc = GET_ALLOC(HDRP(next));
    size_t next_size = GET_SIZE(HDRP(next));
    void* prev = PREV_BLKP(ptr);
    size_t prev_alloc = GET_ALLOC(FTRP(prev));
    size_t prev_size = GET_SIZE(HDRP(prev));


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

    else if(!next_alloc && (old_size + next_size) >= asize){
        //next는 free list안에 있으므로 먼저 제거
        remove_node(next);

        size_t new_size = old_size + next_size;

        PUT(HDRP(ptr), PACK(new_size, 1));
        PUT(FTRP(ptr), PACK(new_size, 1));
        // PUT(HDRP(ptr), PACK(new_size, 0));
        // place(ptr, asize);


        return ptr;
    }

    // prev 가용 블록 흡수해서 확장 (데이터 이동 필요)
    

    else if (!prev_alloc && !next_alloc && (prev_size + old_size + next_size) >= asize) {
        remove_node(prev);
        remove_node(next);

        void *newptr = prev;
        size_t new_size = prev_size + old_size + next_size;

        memmove(newptr, ptr, old_payload);
        
        PUT(HDRP(newptr), PACK(new_size, 1));
        PUT(FTRP(newptr), PACK(new_size, 1));
        // PUT(HDRP(prev), PACK(new_size, 1));
        // place(prev, asize);
        
        return newptr;
    }

    else if (!prev_alloc && (prev_size + old_size) >= asize) {
        remove_node(prev);

        void *newptr  = prev;
        size_t new_size = prev_size + old_size;

        // 먼저 안전하게 데이터 이동
        memmove(newptr, ptr, old_payload);
        
        PUT(HDRP(newptr), PACK(new_size, 1));
        PUT(FTRP(newptr), PACK(new_size, 1));
        // PUT(HDRP(prev), PACK(new_size, 0));
        // place(prev, asize);
        
        return newptr;
    }

    // prev + next 모두 가용이면 둘 다 흡수
    
    // 마지막에 있을 경우
    
    // 새로 할당해서 복사
    void *newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;

    size_t copy = (old_payload < size) ? old_payload : size;
    memcpy(newptr, ptr, copy);
    mm_free(ptr);
    return newptr;

}

//반납된 가용 블록을 bins 리스트에 다시 넣는 역할을 하는 함수
static void insert_node(void* bp){
    size_t sz = GET_SIZE(HDRP(bp));
    int i = bin_index(sz);

    //크기가 작은 블록들을 확인
    if (i <= 9) { // 작은 bin만 정렬 삽입
        void* p = bins[i];
        void* prev = NULL;
        //새로 들어온 bp보다 크기가 작은 블록들은 모두 지나친다.
        while (p && GET_SIZE(HDRP(p)) < sz){
            prev = p;
            p = SUCC(p);
        }
        //자신보다 크거나 같은 블록을 만나면 바로 앞에 자신의 위치를 잡고 삽입된다.
        PRED(bp) = prev;
        SUCC(bp) = p;
        if (prev) SUCC(prev) = bp; else bins[i] = bp;
        if (p)    PRED(p) = bp;
    } else {
        // 큰 bin은 LIFO로 충분히 빠름
        // 리스트를 탐색하는 과정이 없다.
        PRED(bp) = NULL;
        SUCC(bp) = bins[i]; // 새 블록(bp)의 다음을 첫 번째 블록으로 지정
        if (bins[i]) PRED(bins[i]) = bp; // 기존 첫 번째 블록의 이전을 새 블록으로 지정
        bins[i] = bp; //첫 번째 블록을 이제 막 들어온 새 블록으로 교체
    }
}

//연결리스트에서 특정 노드를 제거하는 함수
static void remove_node(void* bp){
    void* prev = PRED(bp);
    void* next = SUCC(bp);
 
    size_t sz = GET_SIZE(HDRP(bp));
    int i = bin_index(sz);

    if(prev) {SUCC(prev) = next;} else {bins[i] = next;}
    if(next) {PRED(next) = prev;}
}

static inline int bin_index(size_t asize){
    if(asize <= 32) return 0;
    if(asize <= 48) return 1;
    if(asize <= 64) return 2;
    if(asize <= 80) return 3;
    if(asize <= 96) return 4;
    if(asize <= 128) return 5;
    if(asize <= 192) return 6;
    if(asize <= 256) return 7;
    if(asize <= 384) return 8;
    if(asize <= 512) return 9;

    int idx = 10;
    size_t sz = 1024;
    // 최소 16B(= 2*DSIZE) 가정
    if(sz < 2*DSIZE) sz = 2*DSIZE;
    while(idx < NUM_BINS-1 && asize > sz){
        sz <<= 1;
        idx++;
    }
    return idx;
}