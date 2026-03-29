/* Ch16 ImplTest runner — calls extracted test functions and prints results. */
#include <stdio.h>
#include "krmlinit.h"
#include "CLRS_Ch16_ActivitySelection_ImplTest.h"
#include "CLRS_Ch16_Huffman_ImplTest.h"

int main(void) {
  krmlinit_globals();
  printf("=== Ch16 ImplTest C Extraction Tests ===\n\n");

  printf("Running Activity Selection test... ");
  CLRS_Ch16_ActivitySelection_ImplTest_test_activity_selection_3();
  printf("PASSED\n");

  printf("Running Huffman Tree test... ");
  CLRS_Ch16_Huffman_ImplTest_test_huffman_2();
  printf("PASSED\n");

  printf("\nAll tests PASSED.\n");
  return 0;
}
