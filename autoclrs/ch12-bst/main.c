/*
  Test driver for CLRS Chapter 12 BST — C extraction test.

  Two layers of assurance:
  1. PROOF: Ghost Pulse assertions (erased at extraction) verify
     postcondition precision and BST validity preservation.
  2. RUNTIME: C-level checks below independently verify the concrete
     output values (search results, min/max values, delete effects).
*/

#include <stdio.h>
#include <stdlib.h>

#include "CLRS_Ch12_BST_TestMain.h"
#include "CLRS_Ch12_BSTArray_TestMain.h"

int main(void) {
  printf("=== CLRS Ch12 BST — Extracted tests ===\n\n");

  /* ── Pointer-based BST test ── */
  printf("--- Pointer-based BST test (insert {2,1,3}, search, min, max, delete) ---\n");
  if (!CLRS_Ch12_BST_TestMain_main()) {
    fprintf(stderr, "FAIL: Pointer-based BST test failed\n");
    return 1;
  }
  printf("  PASS (search, min, max, delete all verified)\n\n");

  /* ── Array-based BST test ── */
  printf("--- Array-based BST test (search empty, insert 5, search found) ---\n");
  if (!CLRS_Ch12_BSTArray_TestMain_main()) {
    fprintf(stderr, "FAIL: Array-based BST test failed\n");
    return 1;
  }
  printf("  PASS (empty search=None, insert succeeded, search found key)\n\n");

  printf("=== All ch12 tests passed ===\n");
  return 0;
}
