/* main.c — Driver for Ch22 ImplTest C extraction tests */
#include <stdio.h>
#include "CLRS_Ch22_ImplTestMain.h"

int main(void) {
  printf("Ch22 ImplTest: running BFS, DFS, TopologicalSort tests...\n");
  CLRS_Ch22_ImplTestMain_run_all_tests();
  printf("Ch22 ImplTest: all tests passed.\n");
  return 0;
}
