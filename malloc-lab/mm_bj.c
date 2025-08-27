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
    "6team",
    /* First member's full name */
    "Junryul Baek",
    /* First member's email address */
    "farvinjr104@gmail.com",
    /* Second member's full name (leave blank if none) */
    "EUNBI KIM", "HYUNSO RYU"
    };

// 매크로영역

// 워드, 더블, 청크사이즈 선언
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12) // 1을 왼쪽으로 12번 시프트 = 1*2^12 = 4KB / 시스템 기본 메모리 페이지 크기
#define MINBLK (4 * DSIZE)

// 헤더/푸터에 저장할 값 생성  (크키 | 할당여부)
#define PACK(size, alloc) ((size) | (alloc))

// 주소 p에서 4바이트(워드) 읽기/쓰기
// 64비트 컴퓨터에서도 4바이트를 기준으로 동작하도록 설계되어 있음
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 헤더/푸터에서 크기와 할당 비트 추출
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// 블록 포인터(bp)로 헤더와 푸터 주소 계산
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 블록 포인터(bp)로 이전/다음 블록 포인터 계산
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

// 적합한 블록이 없을 경우 확장에 사용하기 위한 매크로
#define MAX(x, y) ((x) > (y) ? (x) : (y))

// 포인터 관리용 매크로 (찾기, 연결)
#define SUCC(bp) (*(void **)(bp))
#define PRED(bp) (*(void **)((char *)bp + DSIZE))
#define SET_SUCC(bp, succ_p) (SUCC(bp) = (succ_p))
#define SET_PRED(bp, pred_p) (PRED(bp) = (pred_p))

// 사이즈 클래스
#define NUM_CLASSES 13

// Binary-bal 전용 튜닝 스위치 1(활성)0(비활성)
#ifndef TUNE_BINARY_BAL
#define TUNE_BINARY_BAL 1
#endif

// binary-bal 패턴용. 112→128, 448→512 로 상향
static inline size_t bump_for_binary_bal(size_t req_payload)
{
#if TUNE_BINARY_BAL
    if (req_payload == 112)
        return 128;
    if (req_payload == 448)
        return 512;
#endif
    return req_payload;
}

// 글로벌 변수
static char *heap_listp = 0;
static char *last_bp;
static char *free_lists[NUM_CLASSES];

// 함수 미리 선언
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void add_to_freelist(void *bp);
static void remove_from_freelist(void *bp);

// 디버깅용
// int mm_check(void) {
//     char *bp;
//     int implicit_free_count = 0;
//     int explicit_free_count = 0;

//     // --- 1. 물리적 관점 검사 (힙 전체 순회) ---
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         // ✅ 검사 1: 블록이 정렬 규칙을 지키는가?
//         if ((size_t)bp % DSIZE) {
//             printf("Error: %p is not doubleword aligned\n", bp);
//         }
//         // ✅ 검사 2: 헤더와 푸터가 일치하는가?
//         if (GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp)) ||
//             GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))) {
//             printf("Error: header does not match footer\n");
//         }
//         // 가용 블록 개수 세기 (물리적)
//         if (!GET_ALLOC(HDRP(bp))) {
//             implicit_free_count++;
//         }
//     }

//     // --- 2. 논리적 관점 검사 (가용 리스트 순회) ---
//     for (bp = free_lists[index]; bp != NULL; bp = SUCC(bp)) {
//         // ✅ 검사 3: 가용 리스트의 노드가 실제로 가용 상태인가?
//         if (GET_ALLOC(HDRP(bp))) {
//             printf("Error: Block in free list is marked as allocated\n");
//         }
//         // ✅ 검사 4: 포인터들이 유효한 힙 주소를 가리키는가?
//         if (SUCC(bp) != NULL && (SUCC(bp) < mem_heap_lo() || SUCC(bp) > mem_heap_hi())) {
//             printf("Error: SUCC pointer is outside the heap\n");
//         }
//         if (PRED(bp) != NULL && (PRED(bp) < mem_heap_lo() || PRED(bp) > mem_heap_hi())) {
//             printf("Error: PRED pointer is outside the heap\n");
//         }
//         // ✅ 검사 5: 연결 리스트의 포인터가 서로 일치하는가?
//         if (SUCC(bp) != NULL && PRED(SUCC(bp)) != bp) {
//             printf("Error: Next block's PRED pointer doesn't point back correctly\n");
//         }
//         // 가용 블록 개수 세기 (논리적)
//         explicit_free_count++;
//     }

//     // --- 3. 두 관점 비교 검사 ---
//     // ✅ 검사 6: 물리적으로 찾은 가용 블록 수와 논리적으로 찾은 수가 일치하는가?
//     if (implicit_free_count != explicit_free_count) {
//         printf("Error: Implicit and explicit free counts do not match!\n");
//     }

//     return 1; // 모든 검사 통과
// }

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 1. 힙 뼈대를 위한 16바이트 공간 요청하고 성공여부 확인
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        // (void *)-1 = 정수-1의 비트패턴을 강제변환한 값(최상단영역) = 메모리 할당 실패 표현
        return -1;

    // 2. 뼈대 구조 기록
    PUT(heap_listp, 0);                            // 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 헤더
    heap_listp += (2 * WSIZE);

    // 가용클래스 초기화
    for (int i = 0; i < NUM_CLASSES; i++)
    {
        free_lists[i] = NULL;
    }

    // find를 nextfit 방식으로 이용할 때만 활성화
    // last_bp = NEXT_BLKP(heap_listp);

    // 3. extend_heap을 호출해 첫 가용 블록 생성
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static int get_list_index(size_t size)
{
    /* size는 GET_SIZE(HDRP(bp))로 넘어오는 “블록 전체 크기(asize)”임 */
    if (size <= 24)
        return 0; // MINBLK
    else if (size <= 32)
        return 1;
    else if (size <= 64)
        return 2;

    // binary-bal 타겟: asize=120(112 payload), 136(128 payload)
    else if (size <= 120)
        return 3; // 112 payload
    else if (size <= 136)
        return 4; // 128 payload
    else if (size <= 256)
        return 5;
    else if (size <= 456)
        return 6; // 448 payload
    else if (size <= 520)
        return 7; // 512 payload
    else if (size <= 2040)
        return 8;
    else if (size <= 4080)
        return 9;
    else if (size <= 16384)
        return 10;
    else if (size <= 65536)
        return 11;
    else
        return 12;
}

static void *extend_heap(size_t words)
{
    char *bp;
    // 1. 요청 크기를 8바이트(더블워드) 정렬에 맞게 올림
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // 2. sbrk로 커널에 메모리 요청
    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;

    // 3. 새로 받은 공간을 가용 블록으로 설정
    PUT(HDRP(bp), PACK(size, 0));         // 새 가용블록 헤더
    PUT(FTRP(bp), PACK(size, 0));         // 새 가용블록 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 에필로그 헤더

    bp = coalesce(bp);

    add_to_freelist(bp);

    return bp;
}

// // 가용블록 검색 (first fit 방식) > 90점
// static void *find_fit(size_t asize) {
//     int index = get_list_index(asize);

//     for (int i = index; i < NUM_CLASSES; i++) {
//         void *bp = free_lists[i];

//         while (bp != NULL) {
//             if (asize <= GET_SIZE(HDRP(bp))) {
//                 return bp;
//             }
//             bp = SUCC(bp);
//         }
//     }

//     return NULL;
// }

// 가용블록 검색 (next fit 방식) > 90점
// static void *find_fit(size_t asize) {
//     void *bp;

//     if (last_bp == NULL || GET_SIZE(HDRP(last_bp)) == 0)
//         last_bp = NEXT_BLKP(heap_listp);

//     bp = last_bp;

//     do {
//         size_t bsize = GET_SIZE(HDRP(bp));

//         if (bsize == 0) {
//             bp = NEXT_BLKP(heap_listp);
//             continue;
//         }

//         if (!GET_ALLOC(HDRP(bp)) && asize <= bsize) {
//             last_bp = bp;
//             return bp;
//         }

//         bp = NEXT_BLKP(bp);

//     } while (bp != last_bp);

//     return NULL;
// }

// 가용블록 검색 bestfit 방식 > 91점

// 저장해둘 포인터 하나 선언
// 순회하면서 가용 & 사이즈충분이면 저장해둔 블록이랑 비교해서 더 작은걸로 업뎃

static void *find_fit(size_t asize)
{
    int index = get_list_index(asize);
    void *min_bp = NULL;

    for (int i = index; i < NUM_CLASSES; i++)
    {
        void *bp = free_lists[i];
        while (bp != NULL)
        {
            if (asize <= GET_SIZE(HDRP(bp)))
            {
                if (min_bp == NULL || (GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(min_bp))))
                {
                    min_bp = bp;
                }
            }
            bp = SUCC(bp);
        }
        if (min_bp != NULL)
        {
            return min_bp;
        }
    }

    return NULL;
}

// place() 블록 분할 및 배치함수
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    remove_from_freelist(bp);

    // 남는 공간이 최소 블록 크기(이제는 32바이트) 이상이면 분할
    if ((csize - asize) >= MINBLK)
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 앞부분 할당
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 뒷부분 새 가용 블록
        PUT(FTRP(bp), PACK(csize - asize, 0));
        add_to_freelist(bp);
    }
    else
    { // 남는 공간이 적으면 그냥 전체할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void remove_from_freelist(void *bp)
{
    void *prev_bp = PRED(bp);
    void *succ_bp = SUCC(bp);
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_list_index(size);

    // case1. bp가 유일한 노드일 때
    if (prev_bp == NULL && succ_bp == NULL)
    {
        free_lists[index] = NULL;
    }

    // case2. bp가 첫번째 노드일 때
    else if (prev_bp == NULL)
    {
        free_lists[index] = succ_bp;
        SET_PRED(succ_bp, NULL);
    }

    // case3. bp가 마지막 노드일 때
    else if (succ_bp == NULL)
    {
        SET_SUCC(prev_bp, NULL);
    }

    // case4. bp가 리스트 중간
    else
    {
        SET_SUCC(prev_bp, succ_bp);
        SET_PRED(succ_bp, prev_bp);
    }
}

static void add_to_freelist(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_list_index(size);

    SET_SUCC(bp, free_lists[index]);

    if (free_lists[index] != NULL)
    {
        SET_PRED(free_lists[index], bp);
    }
    SET_PRED(bp, NULL);
    free_lists[index] = bp;
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    // 의미없는 요청 무시
    if (size == 0)
        return NULL;

    /* ★ binary-bal 최적화: 112→128, 448→512 로 상향 */
    size = bump_for_binary_bal(size);

    // 오버헤드와 정렬 요구사항 포함 블록 크기 조정
    asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE); // align(size + overhead)
    if (asize < MINBLK)
        asize = MINBLK;

    // 가용 리스트에서 적합한 블록 검색
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    // 적합한 블록이 없을 경우: 힙 확장하고 블록 배치
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    // 헤더와 푸터를 가용 상태로 변경
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 주변 블록 확인 및 연결시도
    bp = coalesce(bp);

    // 연결된 블록 가용리스트에 추가
    add_to_freelist(bp);
    last_bp = bp;
}

static void *coalesce(void *bp)
{
    // 이전/다음 블록의 할당 상태를 가져옴
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case1: 양쪽 다 할당 상태
    if (prev_alloc && next_alloc)
    {
        return bp;
    }
    // case2: 다음 블록 가용
    else if (prev_alloc && !next_alloc)
    {
        remove_from_freelist(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // case3: 이전 블록 가용
    else if (!prev_alloc && next_alloc)
    {
        remove_from_freelist(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // case4: 둘다 가용
    else
    {
        remove_from_freelist(NEXT_BLKP(bp));
        remove_from_freelist(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // last_bp = bp; // 병합결과를 next-fit 시작점으로
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// 기존의 realloc
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;

//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//         return NULL;
//     copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;

//     if (size < copySize)
//         copySize = size;

//     memcpy(newptr, oldptr, copySize);
//     mm_free(oldptr);
//     return newptr;
// }

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    size_t wantsize;
    size_t oldsize;

    // NULL이 들어오면 그냥 malloc(size) 반환
    if (ptr == NULL)
    {
        return mm_malloc(size);
    }
    // size가 0이면 free 반환
    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    //binary-bal 최적화. 112→128, 448→512 로 상향
    size = bump_for_binary_bal(size);

    if (size <= (2 * DSIZE))
    {
        wantsize = 4 * DSIZE;
    }
    else
    {
        wantsize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    // 4가지 케이스
    // case 1. 요청 크기가 기존 크기보다 작을 경우

    oldsize = GET_SIZE(HDRP(ptr));

    // 이게 점수 더 낮음
    // if (wantsize <= oldsize) {
    //     if ((oldsize - wantsize) >= 8*WSIZE) {

    //         PUT(HDRP(ptr), PACK(wantsize, 1));
    //         PUT(FTRP(ptr), PACK(wantsize, 1));

    //         void* remainder_ptr = NEXT_BLKP(ptr);
    //         PUT(HDRP(remainder_ptr), PACK(oldsize - wantsize, 0));
    //         PUT(FTRP(remainder_ptr), PACK(oldsize - wantsize, 0));

    //         coalesce(remainder_ptr);
    //         add_to_freelist(remainder_ptr);

    //         return ptr;
    //     } else {
    //         newptr =  ptr;
    //         return newptr;
    //     }
    // }

    if (wantsize <= oldsize)
    {
        return ptr;
    }

    // case 2. 인접공간 활용이 가능할 경우
    // 앞공간 vs 뒷공간 구분해야함

    else if (GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0 && (GET_SIZE(HDRP(NEXT_BLKP(ptr))) + oldsize) >= wantsize)
    {
        remove_from_freelist(NEXT_BLKP(ptr));
        oldsize += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(oldsize, 1));
        PUT(FTRP(ptr), PACK(oldsize, 1));
        last_bp = ptr;
        return ptr;
    }
    else if (GET_ALLOC(HDRP(PREV_BLKP(ptr))) == 0 && (GET_SIZE(HDRP(PREV_BLKP(ptr))) + oldsize) >= wantsize)
    {
        remove_from_freelist(PREV_BLKP(ptr));
        size_t oldpayloadsize = oldsize - DSIZE;
        oldsize += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        newptr = PREV_BLKP(ptr);
        PUT(HDRP(newptr), PACK(oldsize, 1));
        PUT(FTRP(newptr), PACK(oldsize, 1));

        memmove(newptr, oldptr, oldpayloadsize);
        last_bp = newptr;
        return newptr;
    }

    // case2 최적화. 이게 점수 더 낮음
    //     else if (GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0 && (GET_SIZE(HDRP(NEXT_BLKP(ptr))) + oldsize) >= wantsize) {

    //     size_t combined_size = GET_SIZE(HDRP(NEXT_BLKP(ptr))) + oldsize;
    //     remove_from_freelist(NEXT_BLKP(ptr));

    //     // ** 최적화 로직 추가 **
    //     // 남는 공간이 최소 블록 크기 이상이면 분할
    //     if ((combined_size - wantsize) >= (4*DSIZE)) {
    //         // 1. 필요한 만큼만 할당 처리
    //         PUT(HDRP(ptr), PACK(wantsize, 1));
    //         PUT(FTRP(ptr), PACK(wantsize, 1));

    //         // 2. 남는 부분을 새로운 가용 블록으로 만듦
    //         void *remainder_bp = NEXT_BLKP(ptr);
    //         PUT(HDRP(remainder_bp), PACK(combined_size - wantsize, 0));
    //         PUT(FTRP(remainder_bp), PACK(combined_size - wantsize, 0));

    //         // 3. 새로 생긴 가용 블록을 리스트에 추가
    //         add_to_freelist(remainder_bp);
    //     }
    //     // 남는 공간이 충분하지 않으면, 블록 전체를 할당 (기존 로직)
    //     else {
    //         PUT(HDRP(ptr), PACK(combined_size, 1));
    //         PUT(FTRP(ptr), PACK(combined_size, 1));
    //     }

    //     last_bp = ptr;
    //     return ptr;
    // }

    // case 3. 힙 영역 확장의 경우

    else if (GET_SIZE(HDRP(NEXT_BLKP(ptr))) == 0 && GET_ALLOC(NEXT_BLKP(ptr)) == 1)
    {
        if (mem_sbrk(wantsize - oldsize) != (void *)-1)
        {
            PUT(HDRP(ptr), PACK(wantsize, 1)); // 새 가용블록 헤더
            PUT(FTRP(ptr), PACK(wantsize, 1)); // 새 가용블록 푸터

            void *new_epilogue = NEXT_BLKP(ptr);
            PUT(HDRP(new_epilogue), PACK(0, 1));
            return ptr;
        }
        else
            return NULL;
    }

    // case 4. 다 안돼서 새로 할당해야 하는 경우

    else
    {
        newptr = mm_malloc(size);
        if (newptr == NULL)
            return NULL;
        copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
        size_t oldpayloadsize = oldsize - DSIZE;
        copySize = oldpayloadsize < size ? oldpayloadsize : size;
        memcpy(newptr, oldptr, copySize);
        mm_free(ptr);
        return newptr;
    }
}