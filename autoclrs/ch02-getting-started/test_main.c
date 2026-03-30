/*
  Ch02 Test Driver — Minimal verified-test runner.

  Calls the extracted ImplTest functions and checks their boolean return
  values. All test logic (inputs, expected outputs, comparison) lives in
  the verified Pulse code — this file only dispatches and reports.
*/

#include <stdio.h>
#include "InsertionSort.h"
#include "MergeSort.h"

int main(void) {
  printf("=== CLRS Ch02 — Extracted tests ===\n\n");

  printf("--- Insertion Sort tests ---\n");
  if (!CLRS_Ch02_InsertionSort_ImplTest_test_insertion_sort_3()) {
    fprintf(stderr, "FAIL: insertion_sort [3,1,2]\n");
    return 1;
  }
  printf("  PASS: sort [3,1,2] => [1,2,3]\n");

  if (!CLRS_Ch02_InsertionSort_ImplTest_test_insertion_sort_empty()) {
    fprintf(stderr, "FAIL: insertion_sort []\n");
    return 1;
  }
  printf("  PASS: sort [] (empty)\n");

  if (!CLRS_Ch02_InsertionSort_ImplTest_test_insertion_sort_single()) {
    fprintf(stderr, "FAIL: insertion_sort [42]\n");
    return 1;
  }
  printf("  PASS: sort [42] (single)\n\n");

  printf("--- Merge Sort tests ---\n");
  if (!CLRS_Ch02_MergeSort_ImplTest_test_merge_sort_3()) {
    fprintf(stderr, "FAIL: merge_sort [3,1,2]\n");
    return 1;
  }
  printf("  PASS: sort [3,1,2] => [1,2,3]\n");

  if (!CLRS_Ch02_MergeSort_ImplTest_test_merge_sort_empty()) {
    fprintf(stderr, "FAIL: merge_sort []\n");
    return 1;
  }
  printf("  PASS: sort [] (empty)\n");

  if (!CLRS_Ch02_MergeSort_ImplTest_test_merge_sort_single()) {
    fprintf(stderr, "FAIL: merge_sort [42]\n");
    return 1;
  }
  printf("  PASS: sort [42] (single)\n");

  printf("\n=== All ch02 tests passed ===\n");
  return 0;
}
