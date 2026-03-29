/* main.c — Driver for vertex cover extraction test
 *
 * Calls the verified 2-approximation vertex cover algorithm on K₃,
 * prints the cover, and validates the result at runtime.
 */
#include <stdio.h>
#include <stdlib.h>
#include "VertexCoverTest.h"

int main(void) {
    /* --- Run the verified test (alloc, compute, free) --- */
    printf("=== Vertex Cover 2-Approximation: Extraction Test ===\n\n");
    printf("Test 1: test_vertex_cover_triangle (K3)\n");
    CLRS_Ch35_VertexCover_ImplTest_test_vertex_cover_triangle();
    printf("  PASS (function completed without error)\n\n");

    /* --- Run algorithm directly to display cover values --- */
    printf("Test 2: approx_vertex_cover on K3 with output\n");
    /* Build adjacency matrix for K3: [0,1,1, 1,0,1, 1,1,0] */
    krml_checked_int_t adj[9] = {0,1,1, 1,0,1, 1,1,0};
    krml_checked_int_t *cover =
        CLRS_Ch35_VertexCover_Impl_approx_vertex_cover(adj, (size_t)3);

    printf("  Cover: [%d, %d, %d]\n",
           (int)cover[0], (int)cover[1], (int)cover[2]);

    /* Validate: must be one of [1,1,0], [1,0,1], [0,1,1] */
    int c0 = (int)cover[0], c1 = (int)cover[1], c2 = (int)cover[2];
    int count = c0 + c1 + c2;
    int valid =
        (c0 == 1 && c1 == 1 && c2 == 0) ||
        (c0 == 1 && c1 == 0 && c2 == 1) ||
        (c0 == 0 && c1 == 1 && c2 == 1);

    printf("  Count: %d (expected: 2)\n", count);
    printf("  Valid 2-approx cover: %s\n", valid ? "YES" : "NO");

    KRML_HOST_FREE(cover);

    if (!valid) {
        printf("\nFAIL: unexpected cover output\n");
        return 1;
    }

    printf("\nAll tests passed.\n");
    return 0;
}
