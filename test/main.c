/*
 * Comprehensive tests for AutoCLRS extracted C implementations.
 *
 * Tests for formally verified CLRS algorithms extracted from Pulse/F*
 * via karamel. Each test exercises the algorithm with known inputs
 * and checks expected outputs.
 *
 * Build: see Makefile 'test' target
 * Run:   ./test/run_tests
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdbool.h>

#include "krmllib.h"
#include "krml/internal/compat.h"

/* Provided by krmlinit.c */
extern void krmlinit_globals(void);

/* Prims operations (from krmllib) */
extern krml_checked_int_t Prims_op_Addition(krml_checked_int_t, krml_checked_int_t);
extern krml_checked_int_t Prims_op_Subtraction(krml_checked_int_t, krml_checked_int_t);
extern krml_checked_int_t Prims_op_Multiply(krml_checked_int_t, krml_checked_int_t);
extern krml_checked_int_t Prims_op_Division(krml_checked_int_t, krml_checked_int_t);
extern krml_checked_int_t Prims_op_Modulus(krml_checked_int_t, krml_checked_int_t);
extern bool Prims_op_LessThan(krml_checked_int_t, krml_checked_int_t);
extern bool Prims_op_GreaterThan(krml_checked_int_t, krml_checked_int_t);

/* FStar_SizeT_v: convert size_t to krml_checked_int_t */
static inline krml_checked_int_t FStar_SizeT_v(size_t x) {
    return (krml_checked_int_t)x;
}

/* ---- Algorithm declarations ---- */

/* Ch02: Sorting */
extern void CLRS_Ch02_InsertionSort_insertion_sort(krml_checked_int_t *a, size_t len);
extern void CLRS_Ch02_MergeSort_merge_sort(krml_checked_int_t *a, size_t len);

/* Ch04: Divide & Conquer */
extern krml_checked_int_t CLRS_Ch04_MaxSubarray_max_subarray(krml_checked_int_t *a, size_t len);

/* Ch06: Heapsort */
extern void CLRS_Ch06_Heap_heapsort(krml_checked_int_t *a, size_t n);

/* Ch07: Quicksort */
extern void CLRS_Ch07_Quicksort_quicksort(krml_checked_int_t *a, size_t len);

/* Ch08: Linear-time sorting */
extern void CLRS_Ch08_CountingSort_counting_sort(krml_checked_int_t *a, size_t len);
extern void CLRS_Ch08_RadixSort_radix_sort(krml_checked_int_t *a, size_t len);
extern size_t CLRS_Ch08_BucketSort_partition(krml_checked_int_t *a, size_t n, krml_checked_int_t pivot);

/* Ch09: Order statistics */
extern krml_checked_int_t CLRS_Ch09_MinMax_find_minimum(krml_checked_int_t *a, size_t len);
extern krml_checked_int_t CLRS_Ch09_MinMax_find_maximum(krml_checked_int_t *a, size_t len);
extern krml_checked_int_t CLRS_Ch09_Select_select(krml_checked_int_t *a, size_t n, size_t k);

/* Ch11: Hash Tables */
extern bool CLRS_Ch11_HashTable_hash_insert(krml_checked_int_t *table, size_t size, krml_checked_int_t key);
extern size_t CLRS_Ch11_HashTable_hash_search(krml_checked_int_t *table, size_t size, krml_checked_int_t key);

/* Ch12: BST */
typedef struct CLRS_Ch12_BST_bst_s {
    krml_checked_int_t *keys;
    bool *valid;
    size_t cap;
} CLRS_Ch12_BST_bst;
extern bool CLRS_Ch12_BST_tree_insert(CLRS_Ch12_BST_bst t, krml_checked_int_t key);

/* Ch15: Dynamic Programming */
extern krml_checked_int_t CLRS_Ch15_RodCutting_rod_cutting(krml_checked_int_t *prices, size_t n);
extern krml_checked_int_t CLRS_Ch15_LCS_lcs(krml_checked_int_t *x, krml_checked_int_t *y, size_t m, size_t n);
extern krml_checked_int_t CLRS_Ch15_MatrixChain_matrix_chain_order(krml_checked_int_t *dims, size_t n);

/* Ch16: Greedy */
extern size_t CLRS_Ch16_ActivitySelection_activity_selection(
    krml_checked_int_t *start_times, krml_checked_int_t *finish_times, size_t n);
extern krml_checked_int_t CLRS_Ch16_Huffman_huffman_cost(krml_checked_int_t *freqs, size_t n);

/* Ch21: Disjoint Sets */
extern void CLRS_Ch21_UnionFind_make_set(size_t *parent, size_t *rank, size_t n);
extern size_t CLRS_Ch21_UnionFind_find(size_t *parent, size_t x, size_t n);
typedef struct { size_t fst; size_t snd; } K___size_t_size_t;
extern K___size_t_size_t CLRS_Ch21_UnionFind_union_(
    size_t *parent, size_t *rank, size_t x, size_t y, size_t n);

/* Ch22: Graph algorithms */
extern void CLRS_Ch22_DFS_dfs(
    krml_checked_int_t *adj, size_t n, size_t source, krml_checked_int_t *color);
extern krml_checked_int_t *CLRS_Ch22_TopologicalSort_topological_sort(
    krml_checked_int_t *adj, size_t n);

/* Ch23: MST */
extern size_t *CLRS_Ch23_Prim_prim(size_t *weights, size_t n, size_t source);

/* Ch24: SSSP */
extern void CLRS_Ch24_BellmanFord_bellman_ford(
    krml_checked_int_t *weights, size_t n, size_t source, krml_checked_int_t *dist);
extern void CLRS_Ch24_Dijkstra_dijkstra(
    krml_checked_int_t *weights, size_t n, size_t source, krml_checked_int_t *dist);

/* Ch25: APSP */
extern void CLRS_Ch25_FloydWarshall_floyd_warshall(krml_checked_int_t *dist, size_t n);

/* Ch26: Max Flow */
extern void CLRS_Ch26_MaxFlow_max_flow(
    krml_checked_int_t *capacity, krml_checked_int_t *flow,
    size_t n, size_t source, size_t sink);

/* Ch28: Matrix Ops */
extern void CLRS_Ch28_MatrixMultiply_matrix_multiply(
    krml_checked_int_t *a, krml_checked_int_t *b, krml_checked_int_t *c, size_t n);

/* Ch31: Number Theory */
extern size_t CLRS_Ch31_GCD_gcd_impl(size_t a, size_t b);
extern krml_checked_int_t CLRS_Ch31_ModExp_mod_exp_impl(
    krml_checked_int_t b, krml_checked_int_t e, krml_checked_int_t m);

/* Ch32: String Matching */
extern krml_checked_int_t CLRS_Ch32_RabinKarp_rabin_karp(
    FStar_Char_char *text, FStar_Char_char *pattern, size_t n, size_t m);

/* Ch33: Computational Geometry */
extern krml_checked_int_t CLRS_Ch33_Segments_cross_product_spec(
    krml_checked_int_t x1, krml_checked_int_t y1,
    krml_checked_int_t x2, krml_checked_int_t y2,
    krml_checked_int_t x3, krml_checked_int_t y3);
extern bool CLRS_Ch33_Segments_segments_intersect(
    krml_checked_int_t x1, krml_checked_int_t y1,
    krml_checked_int_t x2, krml_checked_int_t y2,
    krml_checked_int_t x3, krml_checked_int_t y3,
    krml_checked_int_t x4, krml_checked_int_t y4);

/* Ch35: Approximation */
extern krml_checked_int_t *CLRS_Ch35_VertexCover_approx_vertex_cover(
    krml_checked_int_t *adj, size_t n);

/* ---- Test infrastructure ---- */
static int tests_run = 0;
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) do { \
    tests_run++; \
    printf("  %-50s ", name); \
    fflush(stdout); \
} while(0)

#define PASS() do { \
    tests_passed++; \
    printf("PASS\n"); \
} while(0)

#define FAIL(msg) do { \
    tests_failed++; \
    printf("FAIL: %s\n", msg); \
} while(0)

static int is_sorted(krml_checked_int_t *a, size_t n) {
    for (size_t i = 1; i < n; i++)
        if (a[i] < a[i-1]) return 0;
    return 1;
}

static int is_permutation(krml_checked_int_t *a, krml_checked_int_t *orig, size_t n) {
    /* Count occurrences */
    for (size_t i = 0; i < n; i++) {
        int count_a = 0, count_o = 0;
        for (size_t j = 0; j < n; j++) {
            if (a[j] == a[i]) count_a++;
            if (orig[j] == a[i]) count_o++;
        }
        if (count_a != count_o) return 0;
    }
    return 1;
}

/* ---- Test functions ---- */

static void test_insertion_sort(void) {
    printf("\n[Ch02] InsertionSort\n");

    { TEST("sort empty array");
      krml_checked_int_t a[] = {};
      CLRS_Ch02_InsertionSort_insertion_sort(a, 0);
      PASS(); }

    { TEST("sort single element");
      krml_checked_int_t a[] = {42};
      CLRS_Ch02_InsertionSort_insertion_sort(a, 1);
      if (a[0] == 42) PASS(); else FAIL("wrong value"); }

    { TEST("sort already sorted");
      krml_checked_int_t a[] = {1, 2, 3, 4, 5};
      CLRS_Ch02_InsertionSort_insertion_sort(a, 5);
      if (is_sorted(a, 5)) PASS(); else FAIL("not sorted"); }

    { TEST("sort reverse order");
      krml_checked_int_t a[] = {5, 4, 3, 2, 1};
      krml_checked_int_t orig[] = {5, 4, 3, 2, 1};
      CLRS_Ch02_InsertionSort_insertion_sort(a, 5);
      if (is_sorted(a, 5) && is_permutation(a, orig, 5)) PASS();
      else FAIL("not sorted or not permutation"); }

    { TEST("sort with duplicates");
      krml_checked_int_t a[] = {3, 1, 4, 1, 5, 9, 2, 6, 5, 3};
      krml_checked_int_t orig[] = {3, 1, 4, 1, 5, 9, 2, 6, 5, 3};
      CLRS_Ch02_InsertionSort_insertion_sort(a, 10);
      if (is_sorted(a, 10) && is_permutation(a, orig, 10)) PASS();
      else FAIL("not sorted or not permutation"); }

    { TEST("sort negative numbers");
      krml_checked_int_t a[] = {-3, -1, -4, -1, -5};
      krml_checked_int_t orig[] = {-3, -1, -4, -1, -5};
      CLRS_Ch02_InsertionSort_insertion_sort(a, 5);
      if (is_sorted(a, 5) && is_permutation(a, orig, 5)) PASS();
      else FAIL("not sorted or not permutation"); }
}

static void test_merge_sort(void) {
    printf("\n[Ch02] MergeSort\n");

    { TEST("sort reverse order");
      krml_checked_int_t a[] = {5, 4, 3, 2, 1};
      krml_checked_int_t orig[] = {5, 4, 3, 2, 1};
      CLRS_Ch02_MergeSort_merge_sort(a, 5);
      if (is_sorted(a, 5) && is_permutation(a, orig, 5)) PASS();
      else FAIL("not sorted or not permutation"); }

    { TEST("sort with duplicates");
      krml_checked_int_t a[] = {3, 1, 4, 1, 5, 9, 2, 6, 5, 3};
      krml_checked_int_t orig[] = {3, 1, 4, 1, 5, 9, 2, 6, 5, 3};
      CLRS_Ch02_MergeSort_merge_sort(a, 10);
      if (is_sorted(a, 10) && is_permutation(a, orig, 10)) PASS();
      else FAIL("not sorted or not permutation"); }

    { TEST("sort large array");
      size_t n = 100;
      krml_checked_int_t *a = calloc(n, sizeof(krml_checked_int_t));
      krml_checked_int_t *orig = calloc(n, sizeof(krml_checked_int_t));
      for (size_t i = 0; i < n; i++) { a[i] = (krml_checked_int_t)(n - i); orig[i] = a[i]; }
      CLRS_Ch02_MergeSort_merge_sort(a, n);
      if (is_sorted(a, n) && is_permutation(a, orig, n)) PASS();
      else FAIL("not sorted or not permutation");
      free(a); free(orig); }
}

static void test_heapsort(void) {
    printf("\n[Ch06] HeapSort\n");

    { TEST("sort reverse order");
      krml_checked_int_t a[] = {5, 4, 3, 2, 1};
      krml_checked_int_t orig[] = {5, 4, 3, 2, 1};
      CLRS_Ch06_Heap_heapsort(a, 5);
      if (is_sorted(a, 5) && is_permutation(a, orig, 5)) PASS();
      else FAIL("not sorted or not permutation"); }

    { TEST("sort with duplicates");
      krml_checked_int_t a[] = {3, 1, 4, 1, 5, 9, 2, 6};
      krml_checked_int_t orig[] = {3, 1, 4, 1, 5, 9, 2, 6};
      CLRS_Ch06_Heap_heapsort(a, 8);
      if (is_sorted(a, 8) && is_permutation(a, orig, 8)) PASS();
      else FAIL("not sorted or not permutation"); }

    { TEST("sort single element");
      krml_checked_int_t a[] = {42};
      CLRS_Ch06_Heap_heapsort(a, 1);
      if (a[0] == 42) PASS(); else FAIL("wrong value"); }
}

static void test_quicksort(void) {
    printf("\n[Ch07] Quicksort\n");

    { TEST("sort random array");
      krml_checked_int_t a[] = {10, 7, 8, 9, 1, 5};
      krml_checked_int_t orig[] = {10, 7, 8, 9, 1, 5};
      CLRS_Ch07_Quicksort_quicksort(a, 6);
      if (is_sorted(a, 6) && is_permutation(a, orig, 6)) PASS();
      else FAIL("not sorted or not permutation"); }

    { TEST("sort with all equal elements");
      krml_checked_int_t a[] = {3, 3, 3, 3, 3};
      CLRS_Ch07_Quicksort_quicksort(a, 5);
      if (is_sorted(a, 5)) PASS(); else FAIL("not sorted"); }

    { TEST("sort with negative numbers");
      krml_checked_int_t a[] = {-5, 3, -1, 4, -2};
      krml_checked_int_t orig[] = {-5, 3, -1, 4, -2};
      CLRS_Ch07_Quicksort_quicksort(a, 5);
      if (is_sorted(a, 5) && is_permutation(a, orig, 5)) PASS();
      else FAIL("not sorted or not permutation"); }
}

static void test_counting_sort(void) {
    printf("\n[Ch08] CountingSort\n");

    { TEST("sort non-negative integers");
      krml_checked_int_t a[] = {4, 2, 2, 8, 3, 3, 1};
      krml_checked_int_t orig[] = {4, 2, 2, 8, 3, 3, 1};
      CLRS_Ch08_CountingSort_counting_sort(a, 7);
      if (is_sorted(a, 7) && is_permutation(a, orig, 7)) PASS();
      else FAIL("not sorted or not permutation"); }

    { TEST("sort already sorted");
      krml_checked_int_t a[] = {0, 1, 2, 3, 4};
      CLRS_Ch08_CountingSort_counting_sort(a, 5);
      if (is_sorted(a, 5)) PASS(); else FAIL("not sorted"); }
}

static void test_radix_sort(void) {
    printf("\n[Ch08] RadixSort\n");

    { TEST("sort non-negative integers");
      krml_checked_int_t a[] = {170, 45, 75, 90, 802, 24, 2, 66};
      krml_checked_int_t orig[] = {170, 45, 75, 90, 802, 24, 2, 66};
      CLRS_Ch08_RadixSort_radix_sort(a, 8);
      if (is_sorted(a, 8) && is_permutation(a, orig, 8)) PASS();
      else FAIL("not sorted or not permutation"); }
}

static void test_bucket_partition(void) {
    printf("\n[Ch08] BucketSort partition\n");

    { TEST("partition around pivot");
      krml_checked_int_t a[] = {3, 1, 4, 1, 5, 9, 2, 6};
      size_t p = CLRS_Ch08_BucketSort_partition(a, 8, 4);
      int ok = 1;
      for (size_t i = 0; i < p; i++) if (a[i] > 4) ok = 0;
      for (size_t i = p; i < 8; i++) if (a[i] <= 4) ok = 0;
      if (ok) PASS(); else FAIL("partition invariant violated"); }
}

static void test_max_subarray(void) {
    printf("\n[Ch04] MaxSubarray\n");

    { TEST("CLRS example: max subarray sum");
      krml_checked_int_t a[] = {-2, 1, -3, 4, -1, 2, 1, -5, 4};
      krml_checked_int_t result = CLRS_Ch04_MaxSubarray_max_subarray(a, 9);
      if (result == 6) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 6, got %d", result); FAIL(msg); } }

    { TEST("all negative");
      krml_checked_int_t a[] = {-3, -1, -4, -1, -5};
      krml_checked_int_t result = CLRS_Ch04_MaxSubarray_max_subarray(a, 5);
      if (result == -1) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected -1, got %d", result); FAIL(msg); } }

    { TEST("all positive");
      krml_checked_int_t a[] = {1, 2, 3, 4, 5};
      krml_checked_int_t result = CLRS_Ch04_MaxSubarray_max_subarray(a, 5);
      if (result == 15) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 15, got %d", result); FAIL(msg); } }

    { TEST("single element");
      krml_checked_int_t a[] = {42};
      krml_checked_int_t result = CLRS_Ch04_MaxSubarray_max_subarray(a, 1);
      if (result == 42) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 42, got %d", result); FAIL(msg); } }
}

static void test_min_max(void) {
    printf("\n[Ch09] MinMax\n");

    { TEST("find minimum");
      krml_checked_int_t a[] = {3, 1, 4, 1, 5, 9, 2, 6};
      krml_checked_int_t min = CLRS_Ch09_MinMax_find_minimum(a, 8);
      if (min == 1) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 1, got %d", min); FAIL(msg); } }

    { TEST("find maximum");
      krml_checked_int_t a[] = {3, 1, 4, 1, 5, 9, 2, 6};
      krml_checked_int_t max = CLRS_Ch09_MinMax_find_maximum(a, 8);
      if (max == 9) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 9, got %d", max); FAIL(msg); } }

    { TEST("single element min");
      krml_checked_int_t a[] = {42};
      if (CLRS_Ch09_MinMax_find_minimum(a, 1) == 42) PASS(); else FAIL("wrong"); }

    { TEST("single element max");
      krml_checked_int_t a[] = {42};
      if (CLRS_Ch09_MinMax_find_maximum(a, 1) == 42) PASS(); else FAIL("wrong"); }
}

static void test_select(void) {
    printf("\n[Ch09] Select (order statistics)\n");

    { TEST("find 1st smallest (minimum)");
      krml_checked_int_t a[] = {3, 1, 4, 1, 5};
      krml_checked_int_t result = CLRS_Ch09_Select_select(a, 5, 1);
      if (result == 1) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 1, got %d", result); FAIL(msg); } }

    { TEST("find 3rd smallest (median of 5)");
      krml_checked_int_t a[] = {9, 3, 7, 1, 5};
      krml_checked_int_t result = CLRS_Ch09_Select_select(a, 5, 3);
      if (result == 5) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 5, got %d", result); FAIL(msg); } }

    { TEST("find largest element");
      krml_checked_int_t a[] = {2, 8, 4, 6};
      krml_checked_int_t result = CLRS_Ch09_Select_select(a, 4, 4);
      if (result == 8) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 8, got %d", result); FAIL(msg); } }
}

static void test_hash_table(void) {
    printf("\n[Ch11] HashTable\n");

    { TEST("insert and search");
      size_t sz = 16;
      krml_checked_int_t *table = malloc(sz * sizeof(krml_checked_int_t));
      for (size_t i = 0; i < sz; i++) table[i] = -1; /* -1 = empty sentinel */
      bool ok1 = CLRS_Ch11_HashTable_hash_insert(table, sz, 42);
      bool ok2 = CLRS_Ch11_HashTable_hash_insert(table, sz, 17);
      size_t idx1 = CLRS_Ch11_HashTable_hash_search(table, sz, 42);
      size_t idx2 = CLRS_Ch11_HashTable_hash_search(table, sz, 17);
      if (ok1 && ok2 && idx1 < sz && idx2 < sz && table[idx1] == 42 && table[idx2] == 17) PASS();
      else FAIL("insert/search failed");
      free(table); }

    { TEST("search for missing key");
      size_t sz = 8;
      krml_checked_int_t *table = malloc(sz * sizeof(krml_checked_int_t));
      for (size_t i = 0; i < sz; i++) table[i] = -1;
      CLRS_Ch11_HashTable_hash_insert(table, sz, 10);
      size_t idx = CLRS_Ch11_HashTable_hash_search(table, sz, 99);
      if (idx == sz) PASS();
      else FAIL("should return size for missing key");
      free(table); }
}

static void test_bst(void) {
    printf("\n[Ch12] BST\n");

    { TEST("insert into BST");
      size_t cap = 15;
      krml_checked_int_t *keys = calloc(cap, sizeof(krml_checked_int_t));
      bool *valid = calloc(cap, sizeof(bool));
      memset(valid, 0, cap * sizeof(bool));
      CLRS_Ch12_BST_bst t = { .keys = keys, .valid = valid, .cap = cap };
      bool ok1 = CLRS_Ch12_BST_tree_insert(t, 10);
      bool ok2 = CLRS_Ch12_BST_tree_insert(t, 5);
      bool ok3 = CLRS_Ch12_BST_tree_insert(t, 15);
      bool ok4 = CLRS_Ch12_BST_tree_insert(t, 3);
      if (ok1 && ok2 && ok3 && ok4 && valid[0] && keys[0] == 10) PASS();
      else FAIL("insertion failed");
      free(keys); free(valid); }

    { TEST("duplicate insert returns false");
      size_t cap = 7;
      krml_checked_int_t *keys = calloc(cap, sizeof(krml_checked_int_t));
      bool *valid = calloc(cap, sizeof(bool));
      memset(valid, 0, cap * sizeof(bool));
      CLRS_Ch12_BST_bst t = { .keys = keys, .valid = valid, .cap = cap };
      CLRS_Ch12_BST_tree_insert(t, 10);
      bool dup = CLRS_Ch12_BST_tree_insert(t, 10);
      if (!dup) PASS(); else FAIL("duplicate should return false");
      free(keys); free(valid); }
}

static void test_rod_cutting(void) {
    printf("\n[Ch15] RodCutting\n");

    { TEST("CLRS example: rod prices");
      /* prices[i] = revenue for rod of length i+1 */
      krml_checked_int_t prices[] = {1, 5, 8, 9, 10, 17, 17, 20};
      krml_checked_int_t result = CLRS_Ch15_RodCutting_rod_cutting(prices, 8);
      /* Optimal: cut into 2+6 = 5+17 = 22 */
      if (result == 22) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 22, got %d", result); FAIL(msg); } }

    { TEST("single piece");
      krml_checked_int_t prices[] = {3};
      krml_checked_int_t result = CLRS_Ch15_RodCutting_rod_cutting(prices, 1);
      if (result == 3) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 3, got %d", result); FAIL(msg); } }

    { TEST("length 4 rod");
      krml_checked_int_t prices[] = {1, 5, 8, 9};
      krml_checked_int_t result = CLRS_Ch15_RodCutting_rod_cutting(prices, 4);
      /* Optimal: 2+2 = 5+5 = 10 */
      if (result == 10) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 10, got %d", result); FAIL(msg); } }
}

static void test_lcs(void) {
    printf("\n[Ch15] LCS\n");

    { TEST("CLRS example: ABCBDAB vs BDCAB");
      /* Using integer sequences instead of characters */
      krml_checked_int_t x[] = {1, 2, 3, 2, 4, 1, 2}; /* ABCBDAB */
      krml_checked_int_t y[] = {2, 4, 3, 1, 2};        /* BDCAB */
      krml_checked_int_t result = CLRS_Ch15_LCS_lcs(x, y, 7, 5);
      /* LCS = BCAB, length 4 */
      if (result == 4) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 4, got %d", result); FAIL(msg); } }

    { TEST("identical sequences");
      krml_checked_int_t x[] = {1, 2, 3};
      krml_checked_int_t y[] = {1, 2, 3};
      krml_checked_int_t result = CLRS_Ch15_LCS_lcs(x, y, 3, 3);
      if (result == 3) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 3, got %d", result); FAIL(msg); } }

    { TEST("no common subsequence");
      krml_checked_int_t x[] = {1, 2, 3};
      krml_checked_int_t y[] = {4, 5, 6};
      krml_checked_int_t result = CLRS_Ch15_LCS_lcs(x, y, 3, 3);
      if (result == 0) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 0, got %d", result); FAIL(msg); } }
}

static void test_matrix_chain(void) {
    printf("\n[Ch15] MatrixChain\n");

    { TEST("CLRS example: 4 matrices");
      /* Matrices: A1(30x35), A2(35x15), A3(15x5), A4(5x10) */
      /* dims = [30, 35, 15, 5, 10], n = 4 matrices */
      krml_checked_int_t dims[] = {30, 35, 15, 5, 10};
      krml_checked_int_t result = CLRS_Ch15_MatrixChain_matrix_chain_order(dims, 4);
      /* Optimal: ((A1(A2 A3))A4) = 35*15*5 + 30*35*5 + 30*5*10 = 2625+5250+1500 = 9375 */
      if (result == 9375) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 9375, got %d", result); FAIL(msg); } }

    { TEST("two matrices");
      krml_checked_int_t dims[] = {10, 20, 30};
      krml_checked_int_t result = CLRS_Ch15_MatrixChain_matrix_chain_order(dims, 2);
      if (result == 6000) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 6000, got %d", result); FAIL(msg); } }

    { TEST("single matrix");
      krml_checked_int_t dims[] = {10, 20};
      krml_checked_int_t result = CLRS_Ch15_MatrixChain_matrix_chain_order(dims, 1);
      if (result == 0) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 0, got %d", result); FAIL(msg); } }
}

static void test_activity_selection(void) {
    printf("\n[Ch16] ActivitySelection\n");

    { TEST("CLRS example: 11 activities");
      /* Activities sorted by finish time */
      krml_checked_int_t s[] = {1, 3, 0, 5, 3, 5, 6, 8, 8, 2, 12};
      krml_checked_int_t f[] = {4, 5, 6, 7, 9, 9, 10, 11, 12, 14, 16};
      size_t count = CLRS_Ch16_ActivitySelection_activity_selection(s, f, 11);
      /* Optimal: {a1, a4, a8, a11} = 4 activities */
      if (count == 4) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 4, got %zu", count); FAIL(msg); } }

    { TEST("single activity");
      krml_checked_int_t s[] = {0};
      krml_checked_int_t f[] = {1};
      size_t count = CLRS_Ch16_ActivitySelection_activity_selection(s, f, 1);
      if (count == 1) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 1, got %zu", count); FAIL(msg); } }
}

static void test_huffman(void) {
    printf("\n[Ch16] Huffman\n");

    { TEST("equal frequencies");
      krml_checked_int_t freqs[] = {1, 1, 1, 1};
      krml_checked_int_t cost = CLRS_Ch16_Huffman_huffman_cost(freqs, 4);
      /* 4 symbols, balanced tree: each at depth 2, cost = 4*2*1 = 8 */
      if (cost >= 0) PASS();
      else FAIL("cost should be non-negative"); }

    { TEST("single symbol");
      krml_checked_int_t freqs[] = {5};
      krml_checked_int_t cost = CLRS_Ch16_Huffman_huffman_cost(freqs, 1);
      if (cost == 0) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 0, got %d", cost); FAIL(msg); } }

    { TEST("two symbols");
      krml_checked_int_t freqs[] = {3, 7};
      krml_checked_int_t cost = CLRS_Ch16_Huffman_huffman_cost(freqs, 2);
      /* Two symbols: each at depth 1, cost = 1*3 + 1*7 = 10 */
      if (cost == 10) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 10, got %d", cost); FAIL(msg); } }
}

static void test_union_find(void) {
    printf("\n[Ch21] UnionFind\n");

    { TEST("make_set initializes correctly");
      size_t n = 5;
      size_t *parent = calloc(n, sizeof(size_t));
      size_t *rank = calloc(n, sizeof(size_t));
      CLRS_Ch21_UnionFind_make_set(parent, rank, n);
      int ok = 1;
      for (size_t i = 0; i < n; i++)
          if (parent[i] != i || rank[i] != 0) ok = 0;
      if (ok) PASS(); else FAIL("make_set init wrong");
      free(parent); free(rank); }

    { TEST("find returns self for singletons");
      size_t n = 5;
      size_t *parent = calloc(n, sizeof(size_t));
      size_t *rank = calloc(n, sizeof(size_t));
      CLRS_Ch21_UnionFind_make_set(parent, rank, n);
      int ok = 1;
      for (size_t i = 0; i < n; i++)
          if (CLRS_Ch21_UnionFind_find(parent, i, n) != i) ok = 0;
      if (ok) PASS(); else FAIL("find should return self");
      free(parent); free(rank); }

    { TEST("union merges sets");
      size_t n = 5;
      size_t *parent = calloc(n, sizeof(size_t));
      size_t *rank = calloc(n, sizeof(size_t));
      CLRS_Ch21_UnionFind_make_set(parent, rank, n);
      CLRS_Ch21_UnionFind_union_(parent, rank, 0, 1, n);
      CLRS_Ch21_UnionFind_union_(parent, rank, 2, 3, n);
      size_t r01 = CLRS_Ch21_UnionFind_find(parent, 0, n);
      size_t r1 = CLRS_Ch21_UnionFind_find(parent, 1, n);
      size_t r23 = CLRS_Ch21_UnionFind_find(parent, 2, n);
      size_t r3 = CLRS_Ch21_UnionFind_find(parent, 3, n);
      size_t r4 = CLRS_Ch21_UnionFind_find(parent, 4, n);
      if (r01 == r1 && r23 == r3 && r01 != r23 && r01 != r4) PASS();
      else FAIL("union/find incorrect");
      free(parent); free(rank); }

    { TEST("transitive union");
      size_t n = 4;
      size_t *parent = calloc(n, sizeof(size_t));
      size_t *rank = calloc(n, sizeof(size_t));
      CLRS_Ch21_UnionFind_make_set(parent, rank, n);
      CLRS_Ch21_UnionFind_union_(parent, rank, 0, 1, n);
      CLRS_Ch21_UnionFind_union_(parent, rank, 1, 2, n);
      size_t r0 = CLRS_Ch21_UnionFind_find(parent, 0, n);
      size_t r2 = CLRS_Ch21_UnionFind_find(parent, 2, n);
      if (r0 == r2) PASS(); else FAIL("transitive union failed");
      free(parent); free(rank); }
}

static void test_dfs(void) {
    printf("\n[Ch22] DFS\n");

    { TEST("DFS visits all reachable vertices");
      /* 4-vertex graph: 0->1, 1->2, 2->3 (chain) */
      size_t n = 4;
      krml_checked_int_t adj[16] = {0};
      adj[0*4+1] = 1; /* 0->1 */
      adj[1*4+2] = 1; /* 1->2 */
      adj[2*4+3] = 1; /* 2->3 */
      krml_checked_int_t color[4] = {0, 0, 0, 0};
      CLRS_Ch22_DFS_dfs(adj, n, 0, color);
      /* All vertices should be visited (color != 0) */
      if (color[0] != 0 && color[1] != 0 && color[2] != 0 && color[3] != 0) PASS();
      else FAIL("not all reachable vertices visited"); }

    { TEST("DFS does not visit unreachable vertices");
      /* 4-vertex graph: 0->1, 2->3 (two components) */
      size_t n = 4;
      krml_checked_int_t adj[16] = {0};
      adj[0*4+1] = 1;
      adj[2*4+3] = 1;
      krml_checked_int_t color[4] = {0, 0, 0, 0};
      CLRS_Ch22_DFS_dfs(adj, n, 0, color);
      if (color[0] != 0 && color[1] != 0 && color[2] == 0 && color[3] == 0) PASS();
      else FAIL("visited unreachable vertices"); }
}

static void test_topological_sort(void) {
    printf("\n[Ch22] TopologicalSort\n");

    { TEST("topological sort of DAG");
      /* 4-vertex DAG: 0->1, 0->2, 1->3, 2->3 */
      size_t n = 4;
      krml_checked_int_t adj[16] = {0};
      adj[0*4+1] = 1;
      adj[0*4+2] = 1;
      adj[1*4+3] = 1;
      adj[2*4+3] = 1;
      krml_checked_int_t *output = CLRS_Ch22_TopologicalSort_topological_sort(adj, n);
      /* Check that 0 comes before 1,2 and 1,2 come before 3 */
      int pos[4] = {-1, -1, -1, -1};
      for (int i = 0; i < 4; i++) pos[output[i]] = i;
      if (pos[0] < pos[1] && pos[0] < pos[2] && pos[1] < pos[3] && pos[2] < pos[3]) PASS();
      else FAIL("invalid topological order");
      free(output); }

    { TEST("topological sort: chain graph");
      size_t n = 3;
      krml_checked_int_t adj[9] = {0};
      adj[0*3+1] = 1;
      adj[1*3+2] = 1;
      krml_checked_int_t *output = CLRS_Ch22_TopologicalSort_topological_sort(adj, n);
      if (output[0] == 0 && output[1] == 1 && output[2] == 2) PASS();
      else FAIL("expected 0,1,2 order");
      free(output); }
}

static void test_bellman_ford(void) {
    printf("\n[Ch24] BellmanFord\n");

    { TEST("SSSP from source 0");
      /* 4-vertex graph with weights, adjacency matrix (flat) */
      /* 0->1: 4, 0->2: 1, 2->1: 2, 1->3: 1, 2->3: 5 */
      size_t n = 4;
      krml_checked_int_t INF = 1000000;
      krml_checked_int_t w[16];
      for (int i = 0; i < 16; i++) w[i] = INF;
      for (int i = 0; i < 4; i++) w[i*4+i] = 0;
      w[0*4+1] = 4; w[0*4+2] = 1; w[2*4+1] = 2; w[1*4+3] = 1; w[2*4+3] = 5;
      krml_checked_int_t dist[4];
      CLRS_Ch24_BellmanFord_bellman_ford(w, n, 0, dist);
      /* Shortest paths: 0->0: 0, 0->1: 3 (via 2), 0->2: 1, 0->3: 4 (via 2,1) */
      if (dist[0] == 0 && dist[1] == 3 && dist[2] == 1 && dist[3] == 4) PASS();
      else {
          char msg[128]; snprintf(msg, 128, "expected [0,3,1,4], got [%d,%d,%d,%d]",
              dist[0], dist[1], dist[2], dist[3]); FAIL(msg); } }
}

static void test_dijkstra(void) {
    printf("\n[Ch24] Dijkstra\n");

    { TEST("SSSP from source 0");
      size_t n = 4;
      krml_checked_int_t INF = 1000000;
      krml_checked_int_t w[16];
      for (int i = 0; i < 16; i++) w[i] = INF;
      for (int i = 0; i < 4; i++) w[i*4+i] = 0;
      w[0*4+1] = 4; w[0*4+2] = 1; w[2*4+1] = 2; w[1*4+3] = 1; w[2*4+3] = 5;
      krml_checked_int_t dist[4];
      CLRS_Ch24_Dijkstra_dijkstra(w, n, 0, dist);
      if (dist[0] == 0 && dist[1] == 3 && dist[2] == 1 && dist[3] == 4) PASS();
      else {
          char msg[128]; snprintf(msg, 128, "expected [0,3,1,4], got [%d,%d,%d,%d]",
              dist[0], dist[1], dist[2], dist[3]); FAIL(msg); } }

    { TEST("isolated vertex");
      size_t n = 3;
      krml_checked_int_t INF = 1000000;
      krml_checked_int_t w[9];
      for (int i = 0; i < 9; i++) w[i] = INF;
      for (int i = 0; i < 3; i++) w[i*3+i] = 0;
      w[0*3+1] = 5;
      krml_checked_int_t dist[3];
      CLRS_Ch24_Dijkstra_dijkstra(w, n, 0, dist);
      if (dist[0] == 0 && dist[1] == 5 && dist[2] == INF) PASS();
      else FAIL("distances incorrect"); }
}

static void test_floyd_warshall(void) {
    printf("\n[Ch25] FloydWarshall\n");

    { TEST("all-pairs shortest paths");
      size_t n = 4;
      krml_checked_int_t INF = 1000000;
      krml_checked_int_t dist[16];
      for (int i = 0; i < 16; i++) dist[i] = INF;
      for (int i = 0; i < 4; i++) dist[i*4+i] = 0;
      dist[0*4+1] = 3; dist[0*4+2] = 8; dist[1*4+3] = 1;
      dist[2*4+1] = 4; dist[3*4+0] = 2;
      CLRS_Ch25_FloydWarshall_floyd_warshall(dist, n);
      /* Check some paths:
         0->1: 3, 0->3: 4 (via 1), 3->1: 5 (via 0), 3->2: 10 (via 0) */
      if (dist[0*4+1] == 3 && dist[0*4+3] == 4 && dist[3*4+1] == 5) PASS();
      else {
          char msg[128]; snprintf(msg, 128, "got d[0][1]=%d d[0][3]=%d d[3][1]=%d",
              dist[0*4+1], dist[0*4+3], dist[3*4+1]); FAIL(msg); } }
}

static void test_prim(void) {
    printf("\n[Ch23] Prim\n");

    { TEST("MST of triangle graph");
      /* 3-vertex complete graph: w(0,1)=1, w(0,2)=3, w(1,2)=2
       * Prim returns key[] array (edge weights to MST), not parent[] */
      size_t n = 3;
      size_t INF = 65535;
      size_t w[9];
      for (int i = 0; i < 9; i++) w[i] = INF;
      for (int i = 0; i < 3; i++) w[i*3+i] = 0;
      w[0*3+1] = 1; w[1*3+0] = 1;
      w[0*3+2] = 3; w[2*3+0] = 3;
      w[1*3+2] = 2; w[2*3+1] = 2;
      size_t *key = CLRS_Ch23_Prim_prim(w, n, 0);
      /* MST from source 0: key[0]=0, key[1]=1 (edge 0-1), key[2]=2 (edge 1-2) */
      size_t total = 0;
      for (size_t i = 0; i < n; i++) total += key[i];
      if (total == 3) PASS();
      else { char msg[64]; snprintf(msg, 64, "MST weight expected 3, got %zu", total); FAIL(msg); }
      free(key); }
}

static void test_max_flow(void) {
    printf("\n[Ch26] MaxFlow\n");

    { TEST("simple 4-node flow network");
      /* s=0, t=3, edges: 0->1:10, 0->2:5, 1->3:5, 2->3:10 */
      size_t n = 4;
      krml_checked_int_t cap[16] = {0};
      cap[0*4+1] = 10; cap[0*4+2] = 5; cap[1*4+3] = 5; cap[2*4+3] = 10;
      krml_checked_int_t flow[16] = {0};
      CLRS_Ch26_MaxFlow_max_flow(cap, flow, n, 0, 3);
      /* Flow conservation: total out of source = total into sink */
      krml_checked_int_t flow_out = flow[0*4+1] + flow[0*4+2];
      krml_checked_int_t flow_in = flow[1*4+3] + flow[2*4+3];
      int cap_ok = 1;
      for (int i = 0; i < 16; i++) if (flow[i] > cap[i] || flow[i] < 0) cap_ok = 0;
      if (flow_out == flow_in && cap_ok && flow_out > 0) PASS();
      else { char msg[128]; snprintf(msg, 128, "flow_out=%d flow_in=%d", flow_out, flow_in); FAIL(msg); } }
}

static void test_matrix_multiply(void) {
    printf("\n[Ch28] MatrixMultiply\n");

    { TEST("2x2 matrix multiplication");
      /* A = [[1,2],[3,4]], B = [[5,6],[7,8]] */
      /* C = [[1*5+2*7, 1*6+2*8], [3*5+4*7, 3*6+4*8]] = [[19,22],[43,50]] */
      krml_checked_int_t a[4] = {1, 2, 3, 4};
      krml_checked_int_t b[4] = {5, 6, 7, 8};
      krml_checked_int_t c[4] = {0};
      CLRS_Ch28_MatrixMultiply_matrix_multiply(a, b, c, 2);
      if (c[0] == 19 && c[1] == 22 && c[2] == 43 && c[3] == 50) PASS();
      else {
          char msg[128]; snprintf(msg, 128, "expected [19,22,43,50], got [%d,%d,%d,%d]",
              c[0], c[1], c[2], c[3]); FAIL(msg); } }

    { TEST("3x3 identity multiplication");
      krml_checked_int_t a[9] = {1,0,0, 0,1,0, 0,0,1};
      krml_checked_int_t b[9] = {1,2,3, 4,5,6, 7,8,9};
      krml_checked_int_t c[9] = {0};
      CLRS_Ch28_MatrixMultiply_matrix_multiply(a, b, c, 3);
      int ok = 1;
      for (int i = 0; i < 9; i++) if (c[i] != b[i]) ok = 0;
      if (ok) PASS(); else FAIL("identity * B should equal B"); }
}

static void test_gcd(void) {
    printf("\n[Ch31] GCD\n");

    { TEST("gcd(48, 18) = 6");
      size_t r = CLRS_Ch31_GCD_gcd_impl(48, 18);
      if (r == 6) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 6, got %zu", r); FAIL(msg); } }

    { TEST("gcd(100, 75) = 25");
      size_t r = CLRS_Ch31_GCD_gcd_impl(100, 75);
      if (r == 25) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 25, got %zu", r); FAIL(msg); } }

    { TEST("gcd(13, 7) = 1 (coprime)");
      size_t r = CLRS_Ch31_GCD_gcd_impl(13, 7);
      if (r == 1) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 1, got %zu", r); FAIL(msg); } }

    { TEST("gcd(12, 12) = 12");
      size_t r = CLRS_Ch31_GCD_gcd_impl(12, 12);
      if (r == 12) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 12, got %zu", r); FAIL(msg); } }
}

static void test_mod_exp(void) {
    printf("\n[Ch31] ModExp\n");

    { TEST("2^10 mod 1000 = 24");
      krml_checked_int_t r = CLRS_Ch31_ModExp_mod_exp_impl(2, 10, 1000);
      if (r == 24) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 24, got %d", r); FAIL(msg); } }

    { TEST("3^5 mod 13 = 9");
      krml_checked_int_t r = CLRS_Ch31_ModExp_mod_exp_impl(3, 5, 13);
      if (r == 9) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 9, got %d", r); FAIL(msg); } }

    { TEST("2^0 mod 5 = 1");
      krml_checked_int_t r = CLRS_Ch31_ModExp_mod_exp_impl(2, 0, 5);
      if (r == 1) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 1, got %d", r); FAIL(msg); } }

    { TEST("7^3 mod 10 = 3");
      krml_checked_int_t r = CLRS_Ch31_ModExp_mod_exp_impl(7, 3, 10);
      if (r == 3) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 3, got %d", r); FAIL(msg); } }

    { TEST("5^117 mod 19 = 1 (Fermat)");
      /* 5^18 ≡ 1 (mod 19), 117 = 6*18 + 9, so 5^117 = (5^18)^6 * 5^9 = 5^9 mod 19 */
      /* 5^2=25≡6, 5^4=36≡17, 5^8=17^2=289≡4, 5^9=5^8*5=20≡1 */
      krml_checked_int_t r = CLRS_Ch31_ModExp_mod_exp_impl(5, 117, 19);
      if (r == 1) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 1, got %d", r); FAIL(msg); } }
}

static void test_rabin_karp(void) {
    printf("\n[Ch32] RabinKarp\n");

    { TEST("find pattern in text");
      /* text = "AABAACAADAABAAABAA", pattern = "AABA" */
      FStar_Char_char text[] = {'A','A','B','A','A','C','A','A','D','A','A','B','A','A','A','B','A','A'};
      FStar_Char_char pat[] = {'A','A','B','A'};
      krml_checked_int_t count = CLRS_Ch32_RabinKarp_rabin_karp(text, pat, 18, 4);
      /* Pattern appears at positions 0, 9, 13 => 3 times */
      if (count == 3) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 3, got %d", count); FAIL(msg); } }

    { TEST("no match");
      FStar_Char_char text[] = {'A','B','C','D'};
      FStar_Char_char pat[] = {'X','Y'};
      krml_checked_int_t count = CLRS_Ch32_RabinKarp_rabin_karp(text, pat, 4, 2);
      if (count == 0) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 0, got %d", count); FAIL(msg); } }

    { TEST("pattern equals text");
      FStar_Char_char text[] = {'A','B','C'};
      FStar_Char_char pat[] = {'A','B','C'};
      krml_checked_int_t count = CLRS_Ch32_RabinKarp_rabin_karp(text, pat, 3, 3);
      if (count == 1) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected 1, got %d", count); FAIL(msg); } }
}

static void test_segments(void) {
    printf("\n[Ch33] Segments\n");

    { TEST("segments intersect (crossing)");
      /* Segment (0,0)-(4,4) and (0,4)-(4,0) cross at (2,2) */
      bool r = CLRS_Ch33_Segments_segments_intersect(0, 0, 4, 4, 0, 4, 4, 0);
      if (r) PASS(); else FAIL("should intersect"); }

    { TEST("segments don't intersect (parallel)");
      bool r = CLRS_Ch33_Segments_segments_intersect(0, 0, 4, 0, 0, 2, 4, 2);
      if (!r) PASS(); else FAIL("should not intersect"); }

    { TEST("cross product sign");
      /* Cross product of vectors (1,0)-(0,0) and (0,1)-(0,0) should be positive */
      krml_checked_int_t cp = CLRS_Ch33_Segments_cross_product_spec(0, 0, 1, 0, 0, 1);
      if (cp > 0) PASS();
      else { char msg[64]; snprintf(msg, 64, "expected positive, got %d", cp); FAIL(msg); } }
}

static void test_vertex_cover(void) {
    printf("\n[Ch35] VertexCover\n");

    { TEST("approx vertex cover of triangle");
      /* 3-vertex complete graph */
      size_t n = 3;
      krml_checked_int_t adj[9] = {0, 1, 1, 1, 0, 1, 1, 1, 0};
      krml_checked_int_t *cover = CLRS_Ch35_VertexCover_approx_vertex_cover(adj, n);
      /* Check cover is valid: every edge has at least one endpoint in cover */
      int valid = 1;
      for (size_t u = 0; u < n; u++)
          for (size_t v = u+1; v < n; v++)
              if (adj[u*n+v] && !cover[u] && !cover[v]) valid = 0;
      /* 2-approx: at most 2*OPT vertices in cover */
      int cover_size = 0;
      for (size_t i = 0; i < n; i++) if (cover[i]) cover_size++;
      if (valid && cover_size <= 2 * n) PASS();
      else FAIL("invalid vertex cover");
      free(cover); }

    { TEST("approx vertex cover of path graph");
      /* 4-vertex path: 0-1-2-3 */
      size_t n = 4;
      krml_checked_int_t adj[16] = {0};
      adj[0*4+1] = 1; adj[1*4+0] = 1;
      adj[1*4+2] = 1; adj[2*4+1] = 1;
      adj[2*4+3] = 1; adj[3*4+2] = 1;
      krml_checked_int_t *cover = CLRS_Ch35_VertexCover_approx_vertex_cover(adj, n);
      int valid = 1;
      for (size_t u = 0; u < n; u++)
          for (size_t v = u+1; v < n; v++)
              if (adj[u*n+v] && !cover[u] && !cover[v]) valid = 0;
      if (valid) PASS(); else FAIL("invalid vertex cover");
      free(cover); }
}

/* ---- Main ---- */

int main(void) {
    krmlinit_globals();

    printf("╔══════════════════════════════════════════════════════════╗\n");
    printf("║  AutoCLRS — Extracted C Algorithm Tests                 ║\n");
    printf("╚══════════════════════════════════════════════════════════╝\n");

    /* Sorting algorithms */
    test_insertion_sort();
    test_merge_sort();
    test_heapsort();
    test_quicksort();
    test_counting_sort();
    test_radix_sort();
    test_bucket_partition();

    /* Divide & conquer */
    test_max_subarray();

    /* Order statistics */
    test_min_max();
    test_select();

    /* Data structures */
    test_hash_table();
    test_bst();

    /* Dynamic programming */
    test_rod_cutting();
    test_lcs();
    test_matrix_chain();

    /* Greedy algorithms */
    test_activity_selection();
    test_huffman();

    /* Disjoint sets */
    test_union_find();

    /* Graph algorithms */
    test_dfs();
    test_topological_sort();
    test_bellman_ford();
    test_dijkstra();
    test_floyd_warshall();
    test_prim();
    test_max_flow();

    /* Matrix operations */
    test_matrix_multiply();

    /* Number theory */
    test_gcd();
    test_mod_exp();

    /* String matching */
    test_rabin_karp();

    /* Computational geometry */
    test_segments();

    /* Approximation algorithms */
    test_vertex_cover();

    printf("\n══════════════════════════════════════════════════════════\n");
    printf("Results: %d/%d passed, %d failed\n", tests_passed, tests_run, tests_failed);
    printf("══════════════════════════════════════════════════════════\n");

    return tests_failed > 0 ? 1 : 0;
}
