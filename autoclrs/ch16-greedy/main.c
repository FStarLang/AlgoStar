/* Ch16 ImplTest runner — calls extracted test functions and checks results. */
#include <stdio.h>
#include <stdlib.h>
#include "CLRS_Ch16_ActivitySelection_ImplTest.h"
#include "CLRS_Ch16_Huffman_ImplTest.h"

int main(void) {
  printf("=== Ch16 ImplTest C Extraction Tests ===\n\n");

  printf("--- Activity Selection test ---\n");
  if (!CLRS_Ch16_ActivitySelection_ImplTest_test_activity_selection_3()) {
    fprintf(stderr, "FAIL: Activity Selection output mismatch\n");
    return 1;
  }
  printf("  PASS (proof: optimality verified; runtime: count=2, sel=[0,2])\n\n");

  printf("--- Huffman Tree test ---\n");
  if (!CLRS_Ch16_Huffman_ImplTest_test_huffman_2()) {
    fprintf(stderr, "FAIL: Huffman Tree test failed\n");
    return 1;
  }
  printf("  PASS (proof: cost=8, WPL-optimal; runtime: input preserved)\n\n");

  printf("=== All ch16 tests passed ===\n");
  return 0;
}
