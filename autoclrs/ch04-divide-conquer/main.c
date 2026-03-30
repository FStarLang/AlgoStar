/* Test driver for CLRS Chapter 4 verified implementations.
 *
 * Calls the extracted-to-C test functions for:
 *   - Binary Search (found, not found, empty)
 *   - Matrix Multiply (2x2)
 *   - Kadane's Maximum Subarray (mixed, all-negative)
 *
 * Two layers of assurance:
 *   1. PROOF: Ghost Pulse assertions (erased at extraction) verify
 *      correctness from the specification.
 *   2. RUNTIME: Computational bool checks survive extraction.
 *      main.c validates that every test returns true.
 */

#include <stdio.h>
#include "CLRS_Ch04_BinarySearch_ImplTest_CLRS_Ch04_MatrixMultiply_ImplTest_CLRS_Ch04_MaxSubarray_Kadane_ImplTest.h"

#define CHECK(call, msg) do { \
    if (!(call)) { \
        fprintf(stderr, "FAIL: %s\n", msg); \
        return 1; \
    } \
    printf("PASS\n"); \
} while(0)

int main(void)
{
    printf("=== CLRS Ch04 Verified Algorithm Tests ===\n\n");

    printf("Binary Search - found case... ");
    CHECK(CLRS_Ch04_BinarySearch_ImplTest_test_binary_search_found(),
          "binary_search found");

    printf("Binary Search - not found case... ");
    CHECK(CLRS_Ch04_BinarySearch_ImplTest_test_binary_search_not_found(),
          "binary_search not found");

    printf("Binary Search - empty array... ");
    CHECK(CLRS_Ch04_BinarySearch_ImplTest_test_binary_search_empty(),
          "binary_search empty");

    printf("Matrix Multiply - 2x2... ");
    CHECK(CLRS_Ch04_MatrixMultiply_ImplTest_test_matrix_multiply_2x2(),
          "matrix_multiply 2x2");

    printf("Kadane Max Subarray - mixed array... ");
    CHECK(CLRS_Ch04_MaxSubarray_Kadane_ImplTest_test_kadane_max_subarray(),
          "kadane max_subarray mixed");

    printf("Kadane Max Subarray - all negative... ");
    CHECK(CLRS_Ch04_MaxSubarray_Kadane_ImplTest_test_kadane_all_negative(),
          "kadane max_subarray all_negative");

    printf("\nAll 6 tests passed.\n");
    return 0;
}
