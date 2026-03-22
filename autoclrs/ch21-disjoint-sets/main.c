#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include "CLRS_Ch21_UnionFind_ImplTest.h"

int main(void) {
  printf("=== Union-Find C Extraction Test ===\n\n");

  printf("Running verified test_union_find()... ");
  CLRS_Ch21_UnionFind_ImplTest_test_union_find();
  printf("OK\n\n");

  printf("All tests passed.\n");
  return 0;
}
