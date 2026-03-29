/*
 * test_main.c — C test driver for CLRS Chapter 9 verified algorithms
 *
 * Calls each extracted algorithm on concrete test data and verifies
 * results match the expected values from the F* specification tests.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "CLRS_Ch09_MinMax_Impl.h"
#include "CLRS_Ch09_PartialSelectionSort_Impl.h"
#include "CLRS_Ch09_Quickselect_Impl.h"
#include "CLRS_Ch09_SimultaneousMinMax_Impl.h"
#include "krmlinit.h"

static int tests_run = 0;
static int tests_passed = 0;

#define CHECK(desc, cond)                                    \
  do {                                                       \
    tests_run++;                                             \
    if (cond) {                                              \
      tests_passed++;                                        \
      printf("  PASS: %s\n", desc);                          \
    } else {                                                 \
      printf("  FAIL: %s\n", desc);                          \
    }                                                        \
  } while (0)

/* Helper: allocate and fill a fresh int array [5, 2, 8] */
static krml_checked_int_t *make_test_array(void) {
  krml_checked_int_t *a = malloc(3 * sizeof(krml_checked_int_t));
  a[0] = 5; a[1] = 2; a[2] = 8;
  return a;
}

static void test_find_minimum(void) {
  printf("[MinMax] find_minimum on [5, 2, 8]\n");
  krml_checked_int_t *a = make_test_array();
  krml_checked_int_t result = CLRS_Ch09_MinMax_Impl_find_minimum(a, 3);
  printf("  result = %d\n", (int)result);
  CHECK("min([5,2,8]) == 2", result == 2);
  free(a);
}

static void test_find_maximum(void) {
  printf("[MinMax] find_maximum on [5, 2, 8]\n");
  krml_checked_int_t *a = make_test_array();
  krml_checked_int_t result = CLRS_Ch09_MinMax_Impl_find_maximum(a, 3);
  printf("  result = %d\n", (int)result);
  CHECK("max([5,2,8]) == 8", result == 8);
  free(a);
}

static void test_select(void) {
  printf("[PartialSelectionSort] select on [5, 2, 8]\n");
  krml_checked_int_t *a;

  /* k=1 (1-indexed): expect 2 (smallest) */
  a = make_test_array();
  krml_checked_int_t r1 = CLRS_Ch09_PartialSelectionSort_Impl_select(a, 3, 1);
  printf("  select(k=1) = %d\n", (int)r1);
  CHECK("select([5,2,8], k=1) == 2", r1 == 2);
  free(a);

  /* k=2: expect 5 (median) */
  a = make_test_array();
  krml_checked_int_t r2 = CLRS_Ch09_PartialSelectionSort_Impl_select(a, 3, 2);
  printf("  select(k=2) = %d\n", (int)r2);
  CHECK("select([5,2,8], k=2) == 5", r2 == 5);
  free(a);

  /* k=3: expect 8 (largest) */
  a = make_test_array();
  krml_checked_int_t r3 = CLRS_Ch09_PartialSelectionSort_Impl_select(a, 3, 3);
  printf("  select(k=3) = %d\n", (int)r3);
  CHECK("select([5,2,8], k=3) == 8", r3 == 8);
  free(a);
}

static void test_quickselect(void) {
  printf("[Quickselect] quickselect on [5, 2, 8]\n");
  krml_checked_int_t *a;

  /* k=0 (0-indexed): expect 2 (smallest) */
  a = make_test_array();
  krml_checked_int_t r0 = CLRS_Ch09_Quickselect_Impl_quickselect(a, 3, 0);
  printf("  quickselect(k=0) = %d\n", (int)r0);
  CHECK("quickselect([5,2,8], k=0) == 2", r0 == 2);
  free(a);

  /* k=2: expect 8 (largest) */
  a = make_test_array();
  krml_checked_int_t r2 = CLRS_Ch09_Quickselect_Impl_quickselect(a, 3, 2);
  printf("  quickselect(k=2) = %d\n", (int)r2);
  CHECK("quickselect([5,2,8], k=2) == 8", r2 == 8);
  free(a);
}

static void test_find_minmax(void) {
  printf("[SimultaneousMinMax] find_minmax on [5, 2, 8]\n");
  krml_checked_int_t *a = make_test_array();
  CLRS_Ch09_SimultaneousMinMax_Spec_minmax_result result =
      CLRS_Ch09_SimultaneousMinMax_Impl_find_minmax(a, 3);
  printf("  min = %d, max = %d\n", (int)result.min_val, (int)result.max_val);
  CHECK("find_minmax min == 2", result.min_val == 2);
  CHECK("find_minmax max == 8", result.max_val == 8);
  free(a);
}

static void test_find_minmax_pairs(void) {
  printf("[SimultaneousMinMax] find_minmax_pairs on [5, 2, 8]\n");
  krml_checked_int_t *a = make_test_array();
  CLRS_Ch09_SimultaneousMinMax_Spec_minmax_result result =
      CLRS_Ch09_SimultaneousMinMax_Impl_find_minmax_pairs(a, 3);
  printf("  min = %d, max = %d\n", (int)result.min_val, (int)result.max_val);
  CHECK("find_minmax_pairs min == 2", result.min_val == 2);
  CHECK("find_minmax_pairs max == 8", result.max_val == 8);
  free(a);
}

int main(void) {
  krmlinit_globals();

  printf("=== CLRS Chapter 9: Order Statistics — C Extraction Tests ===\n\n");

  test_find_minimum();
  test_find_maximum();
  printf("\n");
  test_select();
  printf("\n");
  test_quickselect();
  printf("\n");
  test_find_minmax();
  test_find_minmax_pairs();

  printf("\n=== Results: %d/%d tests passed ===\n", tests_passed, tests_run);
  return (tests_passed == tests_run) ? 0 : 1;
}
