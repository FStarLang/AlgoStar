/*
  Test driver for CLRS Chapter 23 MST — C extraction test.

  Calls the verified, extracted ImplTest functions (which contain both
  proof-level ghost assertions and runtime sz_eq checks) and reports
  pass/fail.  All algorithmic logic lives in the extracted F-star/Pulse
  code; this file is a minimal harness.
*/

#include <stdio.h>
#include <stdlib.h>

/* Proof-carrying test functions (ghost assertions erased) */
#include "Ch23_MST.h"

int main(void) {
  printf("=== CLRS Ch23 MST — Extracted tests ===\n\n");

  /* ── Prim: proof + runtime test ── */
  printf("--- Prim test (3-vertex triangle) ---\n");
  if (!CLRS_Ch23_Prim_ImplTest_test_prim_3()) {
    fprintf(stderr, "FAIL: Prim output mismatch\n");
    return 1;
  }
  printf("  PASS (proof: is_mst verified; runtime: key=[0,1,2] parent=[0,0,1])\n\n");

  /* ── Kruskal: proof + runtime test ── */
  printf("--- Kruskal test (3-vertex triangle) ---\n");
  if (!CLRS_Ch23_Kruskal_ImplTest_test_kruskal_satisfiability()) {
    fprintf(stderr, "FAIL: Kruskal output mismatch\n");
    return 1;
  }
  printf("  PASS (proof: is_mst verified; runtime: edges checked)\n\n");

  printf("=== All ch23 tests passed ===\n");
  return 0;
}
