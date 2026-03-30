/* test_main.c — Minimal C driver for ch25 Floyd-Warshall extracted tests.
 *
 * Calls the bool-returning test functions extracted from the verified
 * Pulse ImplTest module. Each function performs runtime checks and
 * returns true on success.
 */

#include <stdio.h>
#include "CLRS_Ch25_FloydWarshall.h"

int main(void) {
    printf("=== Ch25 Floyd-Warshall: Extracted Tests ===\n\n");
    int pass = 0, fail = 0;

    printf("Test 1: floyd_warshall on 3x3 graph ... ");
    if (test_floyd_warshall_impl()) { printf("PASS\n"); pass++; }
    else { printf("FAIL\n"); fail++; }

    printf("Test 2: check_no_negative_cycle (non-negative diagonal) ... ");
    if (test_neg_cycle_check_true()) { printf("PASS\n"); pass++; }
    else { printf("FAIL\n"); fail++; }

    printf("Test 3: check_no_negative_cycle (negative diagonal) ... ");
    if (test_neg_cycle_check_false()) { printf("PASS\n"); pass++; }
    else { printf("FAIL\n"); fail++; }

    printf("Test 4: floyd_warshall_safe on 3x3 graph ... ");
    if (test_floyd_warshall_safe_impl()) { printf("PASS\n"); pass++; }
    else { printf("FAIL\n"); fail++; }

    printf("\n=== Results: %d passed, %d failed ===\n", pass, fail);
    return fail > 0 ? 1 : 0;
}
