/* Test driver for extracted RB-tree code */
#include <stdio.h>
#include "CLRS_Ch13_RBTree_Main.h"

int main(void) {
  printf("RBTree test: starting\n");
  if (!CLRS_Ch13_RBTree_Main_main()) {
    fprintf(stderr, "RBTree test: FAILED\n");
    return 1;
  }
  printf("RBTree test: passed\n");
  return 0;
}
