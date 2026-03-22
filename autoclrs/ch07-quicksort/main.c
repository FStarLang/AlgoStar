/*
  Test driver for CLRS Chapter 7 Quicksort — C extraction test.

  Calls the krml-extracted test functions and also performs
  its own concrete verification of the quicksort output.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "CLRS_Ch07_Quicksort_ImplTest.h"
#include "internal/CLRS_Ch07_Quicksort_Impl.h"

static int test_count = 0;
static int pass_count = 0;

static void check(const char *name, int condition) {
  test_count++;
  if (condition) {
    pass_count++;
    printf("  PASS: %s\n", name);
  } else {
    printf("  FAIL: %s\n", name);
  }
}

/* Run the extracted test functions (ghost assertions erased;
   passing = no crash) */
static void run_extracted_tests(void) {
  printf("=== Extracted test functions (crash = fail) ===\n");

  CLRS_Ch07_Quicksort_ImplTest_test_quicksort_3();
  check("test_quicksort_3 completed", 1);

  CLRS_Ch07_Quicksort_ImplTest_test_quicksort_with_complexity();
  check("test_quicksort_with_complexity completed", 1);

  CLRS_Ch07_Quicksort_ImplTest_test_quicksort_bounded();
  check("test_quicksort_bounded completed", 1);
}

/* Concrete verification: sort [3,1,2] and check result is [1,2,3] */
static void run_concrete_tests(void) {
  printf("=== Concrete verification ===\n");

  /* Test 1: quicksort on [3,1,2] */
  {
    krml_checked_int_t arr[] = {3, 1, 2};
    CLRS_Ch07_Quicksort_Impl_quicksort(arr, (size_t)3U);
    check("quicksort [3,1,2] -> arr[0]==1", arr[0] == 1);
    check("quicksort [3,1,2] -> arr[1]==2", arr[1] == 2);
    check("quicksort [3,1,2] -> arr[2]==3", arr[2] == 3);
  }

  /* Test 2: quicksort_bounded on [3,1,2] */
  {
    krml_checked_int_t arr[] = {3, 1, 2};
    CLRS_Ch07_Quicksort_Impl_quicksort_bounded(arr,
      (krml_checked_int_t)0, (krml_checked_int_t)3);
    check("quicksort_bounded [3,1,2] -> arr[0]==1", arr[0] == 1);
    check("quicksort_bounded [3,1,2] -> arr[1]==2", arr[1] == 2);
    check("quicksort_bounded [3,1,2] -> arr[2]==3", arr[2] == 3);
  }

  /* Test 3: quicksort on already-sorted array */
  {
    krml_checked_int_t arr[] = {1, 2, 3, 4, 5};
    CLRS_Ch07_Quicksort_Impl_quicksort(arr, (size_t)5U);
    check("quicksort [1..5] -> sorted", arr[0]==1 && arr[1]==2 && arr[2]==3 && arr[3]==4 && arr[4]==5);
  }

  /* Test 4: quicksort on reverse-sorted array */
  {
    krml_checked_int_t arr[] = {5, 4, 3, 2, 1};
    CLRS_Ch07_Quicksort_Impl_quicksort(arr, (size_t)5U);
    check("quicksort [5..1] -> sorted", arr[0]==1 && arr[1]==2 && arr[2]==3 && arr[3]==4 && arr[4]==5);
  }

  /* Test 5: single element */
  {
    krml_checked_int_t arr[] = {42};
    CLRS_Ch07_Quicksort_Impl_quicksort(arr, (size_t)1U);
    check("quicksort [42] -> [42]", arr[0] == 42);
  }

  /* Test 6: duplicates */
  {
    krml_checked_int_t arr[] = {3, 1, 2, 1, 3};
    CLRS_Ch07_Quicksort_Impl_quicksort(arr, (size_t)5U);
    check("quicksort [3,1,2,1,3] -> [1,1,2,3,3]",
          arr[0]==1 && arr[1]==1 && arr[2]==2 && arr[3]==3 && arr[4]==3);
  }
}

int main(void) {
  printf("CLRS Chapter 7: Quicksort — C extraction test\n\n");
  run_extracted_tests();
  printf("\n");
  run_concrete_tests();
  printf("\n%d/%d tests passed\n", pass_count, test_count);
  return (pass_count == test_count) ? 0 : 1;
}
