/* Test harness for CLRS Ch26 Max Flow (Edmonds-Karp) C extraction.
   Calls the test functions extracted from CLRS.Ch26.MaxFlow.ImplTest
   and checks their boolean return values. */

#include <stdio.h>
#include <stdbool.h>
#include "CLRS_Ch26_MaxFlow_ImplTest.h"

int main(void) {
  int failures = 0;

  printf("=== CLRS Ch26 Max Flow: C Extraction Test ===\n");

  printf("Test 1: Single-edge network (expected flow = 7) ... ");
  if (CLRS_Ch26_MaxFlow_ImplTest_test_max_flow_completeness()) {
    printf("PASS\n");
  } else {
    printf("FAIL\n");
    failures++;
  }

  printf("Test 2: Disconnected network (expected flow = 0) ... ");
  if (CLRS_Ch26_MaxFlow_ImplTest_test_max_flow_disconnected_completeness()) {
    printf("PASS\n");
  } else {
    printf("FAIL\n");
    failures++;
  }

  printf("Test 3: 3-vertex two-path (expected flow = 20) ... ");
  if (CLRS_Ch26_MaxFlow_ImplTest_test_max_flow_3v()) {
    printf("PASS\n");
  } else {
    printf("FAIL\n");
    failures++;
  }

  printf("Test 4: Diamond 4-vertex (expected flow = 20) ... ");
  if (CLRS_Ch26_MaxFlow_ImplTest_test_max_flow_diamond()) {
    printf("PASS\n");
  } else {
    printf("FAIL\n");
    failures++;
  }

  printf("Test 5: Bottleneck (expected flow = 1) ... ");
  if (CLRS_Ch26_MaxFlow_ImplTest_test_max_flow_bottleneck()) {
    printf("PASS\n");
  } else {
    printf("FAIL\n");
    failures++;
  }

  if (failures == 0) {
    printf("=== All 5 tests passed ===\n");
  } else {
    printf("=== %d test(s) FAILED ===\n", failures);
  }
  return failures;
}
