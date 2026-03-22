/* Main test driver for Counting Sort C extraction */
#include <stdio.h>
#include <stdlib.h>
#include "fstar_sizet_shim.h"
#include "ImplTest.h"

int main(void) {
  printf("=== Counting Sort C Extraction Tests ===\n\n");

  printf("Test 1: counting_sort_inplace [3,1,2] -> [1,2,3] ...\n");
  CLRS_Ch08_CountingSort_ImplTest_test_counting_sort_inplace();
  printf("  PASSED\n\n");

  printf("Test 2: counting_sort_impl [3,1,2] -> [1,2,3] ...\n");
  CLRS_Ch08_CountingSort_ImplTest_test_counting_sort_impl();
  printf("  PASSED\n\n");

  printf("All tests passed.\n");
  return 0;
}
