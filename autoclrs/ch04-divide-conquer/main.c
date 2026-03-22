/* Test driver for CLRS Chapter 4 verified implementations.
 *
 * Calls the extracted-to-C test functions for:
 *   - Binary Search (found, not found, empty)
 *   - Matrix Multiply (2x2)
 *   - Kadane's Maximum Subarray (mixed, all-negative)
 *
 * Each test allocates arrays, runs the verified algorithm, and frees.
 * If the program completes without crashing, all tests pass.
 */

#include <stdio.h>
#include "CLRS_Ch04_BinarySearch_ImplTest_CLRS_Ch04_MatrixMultiply_ImplTest_CLRS_Ch04_MaxSubarray_Kadane_ImplTest.h"

int main(void)
{
    printf("=== CLRS Ch04 Verified Algorithm Tests ===\n\n");

    printf("Binary Search - found case... ");
    CLRS_Ch04_BinarySearch_ImplTest_test_binary_search_found();
    printf("PASS\n");

    printf("Binary Search - not found case... ");
    CLRS_Ch04_BinarySearch_ImplTest_test_binary_search_not_found();
    printf("PASS\n");

    printf("Binary Search - empty array... ");
    CLRS_Ch04_BinarySearch_ImplTest_test_binary_search_empty();
    printf("PASS\n");

    printf("Matrix Multiply - 2x2... ");
    CLRS_Ch04_MatrixMultiply_ImplTest_test_matrix_multiply_2x2();
    printf("PASS\n");

    printf("Kadane Max Subarray - mixed array... ");
    CLRS_Ch04_MaxSubarray_Kadane_ImplTest_test_kadane_max_subarray();
    printf("PASS\n");

    printf("Kadane Max Subarray - all negative... ");
    CLRS_Ch04_MaxSubarray_Kadane_ImplTest_test_kadane_all_negative();
    printf("PASS\n");

    printf("\nAll 6 tests passed.\n");
    return 0;
}
