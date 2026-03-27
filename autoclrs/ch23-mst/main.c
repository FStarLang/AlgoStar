/*
  Test driver for CLRS Chapter 23 MST — C extraction test.
  
  Calls the krml-extracted Prim and Kruskal test functions.
  Ghost assertions are erased during extraction;
  passing = no crash + correct runtime behavior.
*/

#include <stdio.h>
#include <stdlib.h>
#include "CLRS_Ch23_Prim_ImplTest.h"
#include "CLRS_Ch23_Kruskal_ImplTest.h"

int main(void) {
  printf("=== CLRS Ch23 MST — Extracted test functions ===\n\n");

  printf("--- Prim test (3-vertex triangle) ---\n");
  CLRS_Ch23_Prim_ImplTest_test_prim_3();
  printf("  PASS (no crash)\n\n");

  printf("--- Kruskal test (satisfiability) ---\n");
  CLRS_Ch23_Kruskal_ImplTest_test_kruskal_satisfiability();
  printf("  PASS (no crash)\n\n");

  printf("=== All ch23 tests passed ===\n");
  return 0;
}
