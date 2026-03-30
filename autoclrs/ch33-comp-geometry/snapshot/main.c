/* HANDWRITTEN FILE — This is a manually written test driver, not generated code.
 *
 * Test driver for CLRS Ch33 Computational Geometry — C extraction tests.
 *
 * Calls each extracted Pulse test function and checks the boolean result.
 * Each test returns true if all concrete checks passed.
 * The F* verification guarantees correctness of the computed results;
 * this driver independently validates at the C level. */

#include <stdio.h>
#include <stdbool.h>
#include "CLRS_Ch33_Segments_ImplTest_CLRS_Ch33_GrahamScan_ImplTest_CLRS_Ch33_JarvisMarch_ImplTest.h"

#define RUN_TEST(name, func) do { \
    printf("  %-35s ", name); \
    fflush(stdout); \
    if (func()) { \
        printf("PASS\n"); \
        passed++; \
    } else { \
        printf("FAIL\n"); \
        failed++; \
    } \
} while(0)

int main(void)
{
    int passed = 0;
    int failed = 0;

    printf("=== CLRS Ch33 Computational Geometry — C Extraction Tests ===\n\n");

    printf("--- Segments (§33.1) ---\n");
    RUN_TEST("test_cross_product",       CLRS_Ch33_Segments_ImplTest_test_cross_product);
    RUN_TEST("test_direction",           CLRS_Ch33_Segments_ImplTest_test_direction);
    RUN_TEST("test_on_segment",          CLRS_Ch33_Segments_ImplTest_test_on_segment);
    RUN_TEST("test_segments_intersect",  CLRS_Ch33_Segments_ImplTest_test_segments_intersect);

    printf("\n--- Graham Scan (§33.3) ---\n");
    RUN_TEST("test_find_bottom",         CLRS_Ch33_GrahamScan_ImplTest_test_find_bottom);
    RUN_TEST("test_polar_cmp",           CLRS_Ch33_GrahamScan_ImplTest_test_polar_cmp);
    RUN_TEST("test_pop_while",           CLRS_Ch33_GrahamScan_ImplTest_test_pop_while);
    RUN_TEST("test_graham_scan_step",    CLRS_Ch33_GrahamScan_ImplTest_test_graham_scan_step);

    printf("\n--- Jarvis March (§33.3) ---\n");
    RUN_TEST("test_find_leftmost",           CLRS_Ch33_JarvisMarch_ImplTest_test_find_leftmost);
    RUN_TEST("test_find_next",               CLRS_Ch33_JarvisMarch_ImplTest_test_find_next);
    RUN_TEST("test_jarvis_march",            CLRS_Ch33_JarvisMarch_ImplTest_test_jarvis_march);
    RUN_TEST("test_jarvis_march_with_hull",  CLRS_Ch33_JarvisMarch_ImplTest_test_jarvis_march_with_hull);

    printf("\n=== %d passed, %d failed out of %d tests. ===\n",
           passed, failed, passed + failed);
    return failed > 0 ? 1 : 0;
}
