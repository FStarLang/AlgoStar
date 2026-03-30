/* main.c — Driver for vertex cover extraction test
 *
 * Calls the verified test function which returns bool.
 * The proof guarantees the return value is always true;
 * the runtime check confirms this after extraction.
 */
#include <stdio.h>
#include <stdlib.h>
#include "VertexCoverTest.h"

int main(void) {
    printf("=== Vertex Cover 2-Approximation: Extraction Test ===\n\n");

    printf("Test: test_vertex_cover_triangle (K3)\n");
    if (!CLRS_Ch35_VertexCover_ImplTest_test_vertex_cover_triangle()) {
        fprintf(stderr, "  FAIL: cover check failed\n");
        return 1;
    }
    printf("  PASS (proof: is_cover + binary + 2-approx verified; runtime: count=2 confirmed)\n");

    printf("\nAll tests passed.\n");
    return 0;
}
