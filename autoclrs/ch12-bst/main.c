#include <stdio.h>
#include "CLRS_Ch12_BST_TestMain.h"

int main(void) {
  printf("=== CLRS Ch12 BST Pointer-Based Test ===\n");
  printf("Running test_bst_ptr...\n");
  CLRS_Ch12_BST_TestMain_main();
  printf("test_bst_ptr completed successfully.\n");
  printf("All BST operations (insert, search, min, max, delete, free) passed.\n");
  return 0;
}
