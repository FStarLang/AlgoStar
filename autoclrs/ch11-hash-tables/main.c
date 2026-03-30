/*
  Test driver for CLRS Ch11 Hash Table — calls each verified test function
  and checks return values. Each test returns true on success; the ghost
  proofs guarantee the result is always true, and we check at runtime too.
*/

#include "CLRS_Ch11_HashTable_ImplTest.h"
#include <stdio.h>

#define CHECK(fn, name) do { \
    printf("%-32s ... ", name); \
    if (!fn()) { \
        fprintf(stderr, "FAIL\n"); \
        return 1; \
    } \
    printf("PASS\n"); \
} while(0)

int main(void) {
  printf("=== CLRS Ch11 Hash Table — Concrete Execution ===\n");

  CHECK(CLRS_Ch11_HashTable_ImplTest_test_search_empty,        "test_search_empty");
  CHECK(CLRS_Ch11_HashTable_ImplTest_test_insert_then_search,  "test_insert_then_search");
  CHECK(CLRS_Ch11_HashTable_ImplTest_test_insert_search_absent,"test_insert_search_absent");
  CHECK(CLRS_Ch11_HashTable_ImplTest_test_delete_then_search,  "test_delete_then_search");
  CHECK(CLRS_Ch11_HashTable_ImplTest_test_insert_no_dup_existing,"test_insert_no_dup_existing");
  CHECK(CLRS_Ch11_HashTable_ImplTest_test_insert_no_dup_fresh, "test_insert_no_dup_fresh");
  CHECK(CLRS_Ch11_HashTable_ImplTest_test_create_free,         "test_create_free");

  printf("All 7 tests passed.\n");
  return 0;
}
