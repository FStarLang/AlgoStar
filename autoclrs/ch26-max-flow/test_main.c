/* Test harness for CLRS Ch26 Max Flow (Edmonds-Karp) C extraction.
   Calls the two test functions extracted from CLRS.Ch26.MaxFlow.ImplTest. */

#include <stdio.h>
#include "CLRS_Ch26_MaxFlow_ImplTest.h"

int main(void) {
  printf("=== CLRS Ch26 Max Flow: C Extraction Test ===\n");

  printf("Test 1: Single-edge network (expected flow = 7) ... ");
  CLRS_Ch26_MaxFlow_ImplTest_test_max_flow_completeness();
  printf("PASS\n");

  printf("Test 2: Disconnected network (expected flow = 0) ... ");
  CLRS_Ch26_MaxFlow_ImplTest_test_max_flow_disconnected_completeness();
  printf("PASS\n");

  printf("=== All tests passed ===\n");
  return 0;
}
