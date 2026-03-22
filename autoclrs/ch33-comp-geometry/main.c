/* Test driver for CLRS Ch33 Computational Geometry — C extraction tests.
 *
 * Calls each extracted Pulse test function and reports PASS/FAIL.
 * If any function crashes (segfault, abort), the test runner stops.
 * The F* verification guarantees correctness of the computed results;
 * this driver validates the end-to-end extraction pipeline. */

#include <stdio.h>
#include "CLRS_Ch33_Segments_ImplTest_CLRS_Ch33_GrahamScan_ImplTest_CLRS_Ch33_JarvisMarch_ImplTest.h"

#define RUN_TEST(name, func) do { \
    printf("  %-30s ", name); \
    fflush(stdout); \
    func(); \
    printf("PASS\n"); \
    passed++; \
} while(0)

int main(void)
{
    int passed = 0;

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

    printf("\n--- Jarvis March (§33.3) ---\n");
    RUN_TEST("test_find_leftmost",       CLRS_Ch33_JarvisMarch_ImplTest_test_find_leftmost);
    RUN_TEST("test_find_next",           CLRS_Ch33_JarvisMarch_ImplTest_test_find_next);
    RUN_TEST("test_jarvis_march",        CLRS_Ch33_JarvisMarch_ImplTest_test_jarvis_march);

    printf("\n=== All %d tests passed. ===\n", passed);
    return 0;
}
