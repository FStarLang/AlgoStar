/*
  Ch02 Test Driver - Concrete execution test for verified sorting algorithms.

  Tests both InsertionSort and MergeSort on the same inputs used by the
  Pulse proof tests:
    Input:  [3, 1, 2]
    Expected: [1, 2, 3]
  Also tests edge cases: empty array (len=0) and single element (len=1).
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "InsertionSort.h"
#include "internal/MergeSort.h"

static int failures = 0;

static void check_array(const char *label, krml_checked_int_t *arr, size_t len,
                         krml_checked_int_t *expected) {
  int ok = 1;
  for (size_t i = 0; i < len; i++) {
    if (arr[i] != expected[i]) {
      ok = 0;
      break;
    }
  }
  if (ok) {
    printf("  PASS: %s => [", label);
    for (size_t i = 0; i < len; i++) {
      printf("%d%s", arr[i], i + 1 < len ? ", " : "");
    }
    printf("]\n");
  } else {
    printf("  FAIL: %s => got [", label);
    for (size_t i = 0; i < len; i++) {
      printf("%d%s", arr[i], i + 1 < len ? ", " : "");
    }
    printf("], expected [");
    for (size_t i = 0; i < len; i++) {
      printf("%d%s", expected[i], i + 1 < len ? ", " : "");
    }
    printf("]\n");
    failures++;
  }
}

static void test_insertion_sort(void) {
  printf("=== Insertion Sort ===\n");

  /* Test 1: [3, 1, 2] -> [1, 2, 3] */
  {
    krml_checked_int_t arr[] = {3, 1, 2};
    krml_checked_int_t exp[] = {1, 2, 3};
    CLRS_Ch02_InsertionSort_Impl_insertion_sort(arr, 3);
    check_array("sort [3,1,2]", arr, 3, exp);
  }

  /* Test 2: empty array */
  {
    krml_checked_int_t arr[1] = {0}; /* dummy for non-zero-length alloc */
    CLRS_Ch02_InsertionSort_Impl_insertion_sort(arr, 0);
    printf("  PASS: sort [] (empty)\n");
  }

  /* Test 3: single element */
  {
    krml_checked_int_t arr[] = {42};
    krml_checked_int_t exp[] = {42};
    CLRS_Ch02_InsertionSort_Impl_insertion_sort(arr, 1);
    check_array("sort [42]", arr, 1, exp);
  }

  /* Test 4: already sorted */
  {
    krml_checked_int_t arr[] = {1, 2, 3, 4, 5};
    krml_checked_int_t exp[] = {1, 2, 3, 4, 5};
    CLRS_Ch02_InsertionSort_Impl_insertion_sort(arr, 5);
    check_array("sort [1,2,3,4,5]", arr, 5, exp);
  }

  /* Test 5: reverse sorted */
  {
    krml_checked_int_t arr[] = {5, 4, 3, 2, 1};
    krml_checked_int_t exp[] = {1, 2, 3, 4, 5};
    CLRS_Ch02_InsertionSort_Impl_insertion_sort(arr, 5);
    check_array("sort [5,4,3,2,1]", arr, 5, exp);
  }

  /* Test 6: duplicates */
  {
    krml_checked_int_t arr[] = {3, 1, 3, 1, 2};
    krml_checked_int_t exp[] = {1, 1, 2, 3, 3};
    CLRS_Ch02_InsertionSort_Impl_insertion_sort(arr, 5);
    check_array("sort [3,1,3,1,2]", arr, 5, exp);
  }
}

static void test_merge_sort(void) {
  printf("=== Merge Sort ===\n");

  /* Test 1: [3, 1, 2] -> [1, 2, 3] */
  {
    krml_checked_int_t arr[] = {3, 1, 2};
    krml_checked_int_t exp[] = {1, 2, 3};
    CLRS_Ch02_MergeSort_Impl_merge_sort(arr, 3);
    check_array("sort [3,1,2]", arr, 3, exp);
  }

  /* Test 2: empty array */
  {
    krml_checked_int_t arr[1] = {0};
    CLRS_Ch02_MergeSort_Impl_merge_sort(arr, 0);
    printf("  PASS: sort [] (empty)\n");
  }

  /* Test 3: single element */
  {
    krml_checked_int_t arr[] = {42};
    krml_checked_int_t exp[] = {42};
    CLRS_Ch02_MergeSort_Impl_merge_sort(arr, 1);
    check_array("sort [42]", arr, 1, exp);
  }

  /* Test 4: already sorted */
  {
    krml_checked_int_t arr[] = {1, 2, 3, 4, 5};
    krml_checked_int_t exp[] = {1, 2, 3, 4, 5};
    CLRS_Ch02_MergeSort_Impl_merge_sort(arr, 5);
    check_array("sort [1,2,3,4,5]", arr, 5, exp);
  }

  /* Test 5: reverse sorted */
  {
    krml_checked_int_t arr[] = {5, 4, 3, 2, 1};
    krml_checked_int_t exp[] = {1, 2, 3, 4, 5};
    CLRS_Ch02_MergeSort_Impl_merge_sort(arr, 5);
    check_array("sort [5,4,3,2,1]", arr, 5, exp);
  }

  /* Test 6: duplicates */
  {
    krml_checked_int_t arr[] = {3, 1, 3, 1, 2};
    krml_checked_int_t exp[] = {1, 1, 2, 3, 3};
    CLRS_Ch02_MergeSort_Impl_merge_sort(arr, 5);
    check_array("sort [3,1,3,1,2]", arr, 5, exp);
  }
}

int main(void) {
  test_insertion_sort();
  test_merge_sort();

  if (failures == 0) {
    printf("\nAll tests passed.\n");
    return 0;
  } else {
    printf("\n%d test(s) FAILED.\n", failures);
    return 1;
  }
}
