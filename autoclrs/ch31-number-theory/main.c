/*
  Test driver for CLRS Chapter 31 Number Theory — C extraction test.

  Calls the verified, extracted ImplTest functions (which contain both
  proof-level ghost assertions and runtime sz_eq checks) and reports
  pass/fail.  All algorithmic logic lives in the extracted F-star/Pulse
  code; this file is a minimal harness.
*/

#include <stdio.h>
#include <stdlib.h>

/* Proof-carrying test functions (ghost assertions erased) */
#include "Ch31_NumberTheory.h"

int main(void) {
    printf("=== CLRS Ch31 Number Theory — Extracted tests ===\n\n");

    /* ── GCD: proof + runtime test ── */
    printf("--- GCD test: gcd(12, 8) = 4 ---\n");
    if (!CLRS_Ch31_GCD_ImplTest_test_gcd()) {
        fprintf(stderr, "FAIL: GCD output mismatch\n");
        return 1;
    }
    printf("  PASS (proof: divides verified; runtime: result == 4)\n\n");

    /* ── Extended GCD: proof + runtime test ── */
    printf("--- Extended GCD test: extended_gcd(35, 15) = (5, 1, -2) ---\n");
    if (!CLRS_Ch31_ExtendedGCD_ImplTest_test_extended_gcd()) {
        fprintf(stderr, "FAIL: Extended GCD output mismatch\n");
        return 1;
    }
    printf("  PASS (proof: Bezout identity verified; runtime: d == 5)\n\n");

    /* ── ModExp (R-to-L): proof + runtime test ── */
    printf("--- ModExp test: 2^10 mod 100 = 24 ---\n");
    if (!CLRS_Ch31_ModExp_ImplTest_test_mod_exp()) {
        fprintf(stderr, "FAIL: ModExp output mismatch\n");
        return 1;
    }
    printf("  PASS (proof: mod_exp_spec verified; runtime: result == 24)\n\n");

    /* ── ModExpLR (L-to-R): proof + runtime test ── */
    printf("--- ModExpLR test: 3^5 mod 7 = 5 ---\n");
    if (!CLRS_Ch31_ModExpLR_ImplTest_test_mod_exp_lr()) {
        fprintf(stderr, "FAIL: ModExpLR output mismatch\n");
        return 1;
    }
    printf("  PASS (proof: mod_exp_spec verified; runtime: result == 5)\n\n");

    printf("=== All ch31 tests passed ===\n");
    return 0;
}
