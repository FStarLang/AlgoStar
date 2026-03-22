/*
 * main.c — Test driver for CLRS Ch06 Heapsort extracted from Pulse/F*
 *
 * Provides:
 *   - Prims integer operations (extern'd by krml extraction)
 *   - krmlinit_globals override to wire up the BoundedIntegers typeclass dict
 *   - main() entry point calling all 5 test functions
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include "krml/internal/compat.h"
#include "CLRS_Ch06_Heap_ImplTest.h"
#include "internal/CLRS_Ch06_Heap_ImplTest.h"

/* Prims integer operations for krml_checked_int_t (int32_t) */

krml_checked_int_t Prims_op_Addition(krml_checked_int_t x, krml_checked_int_t y) {
  return x + y;
}

krml_checked_int_t Prims_op_Subtraction(krml_checked_int_t x, krml_checked_int_t y) {
  return x - y;
}

krml_checked_int_t Prims_op_Modulus(krml_checked_int_t x, krml_checked_int_t y) {
  return x % y;
}

krml_checked_int_t Prims_op_Division(krml_checked_int_t x, krml_checked_int_t y) {
  return x / y;
}

bool Prims_op_LessThan(krml_checked_int_t x, krml_checked_int_t y) {
  return x < y;
}

bool Prims_op_LessThanOrEqual(krml_checked_int_t x, krml_checked_int_t y) {
  return x <= y;
}

bool Prims_op_GreaterThan(krml_checked_int_t x, krml_checked_int_t y) {
  return x > y;
}

bool Prims_op_GreaterThanOrEqual(krml_checked_int_t x, krml_checked_int_t y) {
  return x >= y;
}

/* Initialize the BoundedIntegers typeclass dict with actual function pointers */
void krmlinit_globals(void) {
  Pulse_Lib_BoundedIntegers_bounded_int_int =
    (Pulse_Lib_BoundedIntegers_bounded_int__krml_checked_int_t){
      .op_Plus             = Prims_op_Addition,
      .op_Subtraction      = Prims_op_Subtraction,
      .op_Less             = Prims_op_LessThan,
      .op_Less_Equals      = Prims_op_LessThanOrEqual,
      .op_Greater          = Prims_op_GreaterThan,
      .op_Greater_Equals   = Prims_op_GreaterThanOrEqual,
      .op_Percent          = Prims_op_Modulus,
      .op_Slash            = Prims_op_Division
    };
}

int main(void) {
  krmlinit_globals();

  printf("CLRS Ch06 Heapsort — Concrete Execution Tests\n");
  printf("==============================================\n");

  printf("Test 1: heapsort [3,1,2] -> [1,2,3] ... ");
  CLRS_Ch06_Heap_ImplTest_test_heapsort_3();
  printf("PASS\n");

  printf("Test 2: build_max_heap [3,1,2] root=3 ... ");
  CLRS_Ch06_Heap_ImplTest_test_build_max_heap_3();
  printf("PASS\n");

  printf("Test 3: heapsort n=0 [5,3,7] unchanged ... ");
  CLRS_Ch06_Heap_ImplTest_test_heapsort_0();
  printf("PASS\n");

  printf("Test 4: heapsort prefix n=2 [7,5,3] -> [5,7,3] ... ");
  CLRS_Ch06_Heap_ImplTest_test_heapsort_prefix();
  printf("PASS\n");

  printf("Test 5: heapsort duplicates [2,1,2] -> [1,2,2] ... ");
  CLRS_Ch06_Heap_ImplTest_test_heapsort_duplicates();
  printf("PASS\n");

  printf("==============================================\n");
  printf("All 5 tests passed.\n");
  return 0;
}
