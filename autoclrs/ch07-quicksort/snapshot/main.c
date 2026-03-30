/*
  *** HANDWRITTEN FILE — NOT GENERATED ***

  Test driver for CLRS Chapter 7 Quicksort — C extraction test.

  Calls the krml-extracted, proof-carrying test functions.
  Each test returns bool: true = all runtime checks passed.
  Ghost assertions (sorted, permutation, complexity bounds) are
  verified by F* and erased at extraction; runtime checks verify
  concrete output values survive to C.
*/

#include <stdio.h>
#include <stdlib.h>
#include "CLRS_Ch07_Quicksort_ImplTest.h"
#include "CLRS_Ch07_Partition_ImplTest.h"

int main(void) {
  printf("CLRS Chapter 7: Quicksort — C extraction test\n\n");

  printf("  test_quicksort_3 ... ");
  if (!CLRS_Ch07_Quicksort_ImplTest_test_quicksort_3()) {
    printf("FAIL\n"); return 1;
  }
  printf("PASS\n");

  printf("  test_quicksort_with_complexity ... ");
  if (!CLRS_Ch07_Quicksort_ImplTest_test_quicksort_with_complexity()) {
    printf("FAIL\n"); return 1;
  }
  printf("PASS\n");

  printf("  test_quicksort_bounded ... ");
  if (!CLRS_Ch07_Quicksort_ImplTest_test_quicksort_bounded()) {
    printf("FAIL\n"); return 1;
  }
  printf("PASS\n");

  printf("  test_partition_3 ... ");
  if (!CLRS_Ch07_Partition_ImplTest_test_partition_3()) {
    printf("FAIL\n"); return 1;
  }
  printf("PASS\n");

  printf("\nAll tests passed\n");
  return 0;
}
