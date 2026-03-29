/* test_main.c — C entry point for ch25 Floyd-Warshall extracted tests.
 *
 * The verified Pulse test functions (ImplTest.fst) are ghost-erased during
 * extraction, so we exercise the extracted API directly from C using the
 * same 3×3 test instance from the specification.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "CLRS_Ch25_FloydWarshall.h"

/* Prims int operations needed by extracted code */
krml_checked_int_t Prims_op_Addition(krml_checked_int_t x, krml_checked_int_t y) {
    return x + y;
}

bool Prims_op_LessThan(krml_checked_int_t x, krml_checked_int_t y) {
    return x < y;
}

#define INF 1000000
#define N   3

static void print_matrix(const char *label, krml_checked_int_t *m, int n) {
    printf("  %s:\n", label);
    for (int i = 0; i < n; i++) {
        printf("    [");
        for (int j = 0; j < n; j++) {
            if (m[i * n + j] >= INF)
                printf(" inf");
            else
                printf(" %3d", (int)m[i * n + j]);
            if (j < n - 1) printf(",");
        }
        printf(" ]\n");
    }
}

/* Expected shortest-path distances (from ImplTest.fst):
 *     0   1   2
 * 0 [ 0   5   20 ]
 * 1 [ 45  0   15 ]
 * 2 [ 30  35  0  ]
 */
static const int expected[9] = { 0, 5, 20, 45, 0, 15, 30, 35, 0 };

static int check_result(krml_checked_int_t *dist, const int *exp, int n) {
    int ok = 1;
    for (int i = 0; i < n * n; i++) {
        if ((int)dist[i] != exp[i]) {
            printf("    MISMATCH at [%d][%d]: got %d, expected %d\n",
                   i / n, i % n, (int)dist[i], exp[i]);
            ok = 0;
        }
    }
    return ok;
}

int main(void) {
    printf("=== Ch25 Floyd-Warshall: Concrete Execution Tests ===\n\n");
    int pass = 0, fail = 0;

    /* Test 1: floyd_warshall on 3×3 graph */
    {
        krml_checked_int_t dist[9] = { 0, 5, INF, 50, 0, 15, 30, INF, 0 };
        printf("Test 1: floyd_warshall on 3x3 graph\n");
        print_matrix("Input", dist, N);
        floyd_warshall(dist, N);
        print_matrix("Output", dist, N);
        if (check_result(dist, expected, N)) {
            printf("  => PASS\n\n");
            pass++;
        } else {
            printf("  => FAIL\n\n");
            fail++;
        }
    }

    /* Test 2: check_no_negative_cycle (true case) */
    {
        krml_checked_int_t dist[9] = { 0, 5, INF, 50, 0, 15, 30, INF, 0 };
        printf("Test 2: check_no_negative_cycle (non-negative diagonal)\n");
        bool ok = check_no_negative_cycle(dist, N);
        printf("  Result: %s (expected: true)\n", ok ? "true" : "false");
        if (ok) {
            printf("  => PASS\n\n");
            pass++;
        } else {
            printf("  => FAIL\n\n");
            fail++;
        }
    }

    /* Test 3: check_no_negative_cycle (false case) */
    {
        krml_checked_int_t dist[9] = { -1, 5, INF, 50, 0, 15, 30, INF, 0 };
        printf("Test 3: check_no_negative_cycle (negative diagonal)\n");
        bool ok = check_no_negative_cycle(dist, N);
        printf("  Result: %s (expected: false)\n", ok ? "true" : "false");
        if (!ok) {
            printf("  => PASS\n\n");
            pass++;
        } else {
            printf("  => FAIL\n\n");
            fail++;
        }
    }

    /* Test 4: floyd_warshall_safe on 3×3 graph */
    {
        krml_checked_int_t dist[9] = { 0, 5, INF, 50, 0, 15, 30, INF, 0 };
        printf("Test 4: floyd_warshall_safe on 3x3 graph\n");
        print_matrix("Input", dist, N);
        floyd_warshall_safe(dist, N);
        print_matrix("Output", dist, N);
        if (check_result(dist, expected, N)) {
            printf("  => PASS\n\n");
            pass++;
        } else {
            printf("  => FAIL\n\n");
            fail++;
        }
    }

    printf("=== Results: %d passed, %d failed ===\n", pass, fail);
    return fail > 0 ? 1 : 0;
}
