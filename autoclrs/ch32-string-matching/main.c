#include <stdio.h>
#include <stdbool.h>
#include "Ch32_StringMatch.h"

int main(void) {
  printf("=== Ch32 String Matching — Concrete Execution Tests ===\n\n");

  printf("[1/3] Naive String Match (CLRS §32.1) ... ");
  fflush(stdout);
  if (!test_naive_string_match()) { printf("FAIL\n"); return 1; }
  printf("PASS\n");

  printf("[2/3] KMP String Match   (CLRS §32.4) ... ");
  fflush(stdout);
  if (!test_kmp_string_match()) { printf("FAIL\n"); return 1; }
  printf("PASS\n");

  printf("[3/3] Rabin-Karp          (CLRS §32.2) ... ");
  fflush(stdout);
  if (!test_rabin_karp()) { printf("FAIL\n"); return 1; }
  printf("PASS\n");

  printf("\nAll 3 tests passed.\n");
  return 0;
}
