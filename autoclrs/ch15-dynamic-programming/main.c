/*
 * Ch15 Dynamic Programming — C test driver for KaRaMeL-extracted code
 *
 * Provides:
 *   - Pulse.Lib.BoundedIntegers typeclass instance initialization
 *   - main() that calls each extracted ImplTest function
 *
 * The algorithm implementations are extracted from verified Pulse code
 * via F* --codegen krml and KaRaMeL.
 */

#include <stdio.h>
#include <stdlib.h>

#include "RodCutting_ImplTest.h"
#include "LCS_ImplTest.h"
#include "MatrixChain_ImplTest.h"
#include "internal/Support.h"
#include "krmlinit.h"

/* Initialize the bounded_int_nat/int instances for Pulse.Lib.BoundedIntegers.
 * The KaRaMeL-generated krmlinit.c declares these as globals with null
 * function pointers; we override them here before calling any test. */
static void init_bounded_int_globals(void) {
  Pulse_Lib_BoundedIntegers_bounded_int_nat =
    (Pulse_Lib_BoundedIntegers_bounded_int__krml_checked_int_t){
      .op_Plus           = Prims_op_Addition,
      .op_Subtraction    = Prims_op_Subtraction,
      .op_Less           = Prims_op_LessThan,
      .op_Less_Equals    = Prims_op_LessThanOrEqual,
      .op_Greater        = Prims_op_GreaterThan,
      .op_Greater_Equals = Prims_op_GreaterThanOrEqual,
      .op_Percent        = Prims_op_Modulus,
      .op_Slash          = Prims_op_Division
    };
  Pulse_Lib_BoundedIntegers_bounded_int_int =
    (Pulse_Lib_BoundedIntegers_bounded_int__krml_checked_int_t){
      .op_Plus           = Prims_op_Addition,
      .op_Subtraction    = Prims_op_Subtraction,
      .op_Less           = Prims_op_LessThan,
      .op_Less_Equals    = Prims_op_LessThanOrEqual,
      .op_Greater        = Prims_op_GreaterThan,
      .op_Greater_Equals = Prims_op_GreaterThanOrEqual,
      .op_Percent        = Prims_op_Modulus,
      .op_Slash          = Prims_op_Division
    };
}

int main(void) {
  init_bounded_int_globals();
  printf("=== Ch15 Dynamic Programming — Extracted C Tests ===\n\n");

  printf("Rod Cutting (extracted from verified Pulse):\n");
  CLRS_Ch15_RodCutting_ImplTest_test_rod_cutting();
  printf("  PASS: rod_cutting completed\n\n");

  printf("LCS (extracted from verified Pulse):\n");
  CLRS_Ch15_LCS_ImplTest_test_lcs();
  printf("  PASS: lcs completed\n\n");

  printf("Matrix Chain (extracted from verified Pulse):\n");
  CLRS_Ch15_MatrixChain_ImplTest_test_matrix_chain();
  printf("  PASS: matrix_chain completed\n\n");

  printf("=== All 3 extracted tests passed ===\n");
  return 0;
}
