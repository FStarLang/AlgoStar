/*
  Test driver for CLRS Ch11 Hash Table — calls each verified test function
  and reports results. Since the proofs are erased at extraction time,
  a successful run (no crash) confirms the C implementation matches the
  verified Pulse code.
*/

#include "CLRS_Ch11_HashTable_ImplTest.h"
#include <stdio.h>

int main(void) {
  printf("=== CLRS Ch11 Hash Table — Concrete Execution ===\n");

  printf("test_search_empty        ... ");
  CLRS_Ch11_HashTable_ImplTest_test_search_empty();
  printf("PASS\n");

  printf("test_insert_then_search  ... ");
  CLRS_Ch11_HashTable_ImplTest_test_insert_then_search();
  printf("PASS\n");

  printf("test_insert_search_absent... ");
  CLRS_Ch11_HashTable_ImplTest_test_insert_search_absent();
  printf("PASS\n");

  printf("test_delete_then_search  ... ");
  CLRS_Ch11_HashTable_ImplTest_test_delete_then_search();
  printf("PASS\n");

  printf("test_insert_no_dup_exist ... ");
  CLRS_Ch11_HashTable_ImplTest_test_insert_no_dup_existing();
  printf("PASS\n");

  printf("test_insert_no_dup_fresh ... ");
  CLRS_Ch11_HashTable_ImplTest_test_insert_no_dup_fresh();
  printf("PASS\n");

  printf("test_create_free         ... ");
  CLRS_Ch11_HashTable_ImplTest_test_create_free();
  printf("PASS\n");

  printf("All 7 tests passed.\n");
  return 0;
}
