/*
 * main.c — Thin C test driver for CLRS Chapter 9 verified algorithms.
 *
 * Calls the extracted proof-carrying test functions, each of which returns
 * bool. The F* proofs guarantee every test returns true; the runtime checks
 * independently verify the results survive extraction correctly.
 */
#include <stdio.h>
#include <stdlib.h>

#include "CLRS_Ch09_MinMax_ImplTest.h"
#include "CLRS_Ch09_PartialSelectionSort_ImplTest.h"
#include "CLRS_Ch09_Quickselect_ImplTest.h"
#include "CLRS_Ch09_SimultaneousMinMax_ImplTest.h"
#include "krmlinit.h"

static int tests_run = 0;
static int tests_passed = 0;

#define RUN_TEST(desc, fn)                                   \
  do {                                                       \
    tests_run++;                                             \
    if (fn()) {                                              \
      tests_passed++;                                        \
      printf("  PASS: %s\n", desc);                          \
    } else {                                                 \
      printf("  FAIL: %s\n", desc);                          \
    }                                                        \
  } while (0)

int main(void) {
  krmlinit_globals();

  printf("=== CLRS Chapter 9: Order Statistics — C Extraction Tests ===\n\n");

  printf("[MinMax]\n");
  RUN_TEST("find_minimum([5,2,8]) == 2",
           CLRS_Ch09_MinMax_ImplTest_test_find_minimum);
  RUN_TEST("find_maximum([5,2,8]) == 8",
           CLRS_Ch09_MinMax_ImplTest_test_find_maximum);

  printf("\n[PartialSelectionSort]\n");
  RUN_TEST("select([5,2,8], k=1) == 2",
           CLRS_Ch09_PartialSelectionSort_ImplTest_test_select_k1);
  RUN_TEST("select([5,2,8], k=2) == 5",
           CLRS_Ch09_PartialSelectionSort_ImplTest_test_select_k2);
  RUN_TEST("select([5,2,8], k=3) == 8",
           CLRS_Ch09_PartialSelectionSort_ImplTest_test_select_k3);

  printf("\n[Quickselect]\n");
  RUN_TEST("quickselect([5,2,8], k=0) == 2",
           CLRS_Ch09_Quickselect_ImplTest_test_quickselect_min);
  RUN_TEST("quickselect([5,2,8], k=2) == 8",
           CLRS_Ch09_Quickselect_ImplTest_test_quickselect_max);

  printf("\n[SimultaneousMinMax]\n");
  RUN_TEST("find_minmax([5,2,8]) min==2 max==8",
           CLRS_Ch09_SimultaneousMinMax_ImplTest_test_find_minmax);
  RUN_TEST("find_minmax_pairs([5,2,8]) min==2 max==8",
           CLRS_Ch09_SimultaneousMinMax_ImplTest_test_find_minmax_pairs);

  printf("\n=== Results: %d/%d tests passed ===\n", tests_passed, tests_run);
  return (tests_passed == tests_run) ? 0 : 1;
}
