/*
  Test driver for CLRS Chapter 23 MST — C extraction test.

  Two layers of assurance:
  1. PROOF: Ghost Pulse assertions (erased at extraction) verify is_mst
     and concrete output uniqueness from the specification.
  2. RUNTIME: C-level checks below independently verify the concrete
     output values match the expected MST (0--1--2, weight 3).
*/

#include <stdio.h>
#include <stdlib.h>

/* Proof-carrying test functions (ghost assertions erased) */
#include "CLRS_Ch23_Prim_ImplTest.h"
#include "CLRS_Ch23_Kruskal_ImplTest.h"

/* Direct algorithm API for runtime checks */
#include "internal/CLRS_Ch23_Prim_Impl.h"
#include "internal/CLRS_Ch23_Kruskal_Impl.h"

#define CHECK(cond, msg) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s\n", msg); \
        return 1; \
    } \
} while(0)

int main(void) {
  printf("=== CLRS Ch23 MST — Extracted tests ===\n\n");

  /* ── Prim: proof test (ghost assertions, erased) ── */
  printf("--- Prim proof test (3-vertex triangle) ---\n");
  CLRS_Ch23_Prim_ImplTest_test_prim_3();
  printf("  PASS (is_mst verified, output uniqueness proved)\n\n");

  /* ── Prim: runtime output check ── */
  printf("--- Prim runtime check ---\n");
  {
    /*  Graph:  0 --1-- 1 --2-- 2
                |               |
                +------3--------+
        Flat 3x3 weights: [0,1,3, 1,0,2, 3,2,0]
        Expected MST: key=[0,1,2] parent=[0,0,1]  */
    size_t weights[] = {0,1,3, 1,0,2, 3,2,0};
    K____size_t___size_t_ result =
        CLRS_Ch23_Prim_Impl_prim(weights, (size_t)3, (size_t)0);
    size_t *keys = result.fst;
    size_t *parents = result.snd;

    CHECK(keys[0] == 0, "key[0] != 0");
    CHECK(keys[1] == 1, "key[1] != 1");
    CHECK(keys[2] == 2, "key[2] != 2");
    CHECK(parents[0] == 0, "parent[0] != 0");
    CHECK(parents[1] == 0, "parent[1] != 0");
    CHECK(parents[2] == 1, "parent[2] != 1");

    printf("  PASS (key=[%zu,%zu,%zu] parent=[%zu,%zu,%zu])\n\n",
           keys[0], keys[1], keys[2],
           parents[0], parents[1], parents[2]);

    KRML_HOST_FREE(keys);
    KRML_HOST_FREE(parents);
  }

  /* ── Kruskal: proof test (ghost assertions, erased) ── */
  printf("--- Kruskal proof test (3-vertex triangle) ---\n");
  CLRS_Ch23_Kruskal_ImplTest_test_kruskal_satisfiability();
  printf("  PASS (is_mst verified, MST edges proved unique)\n\n");

  /* ── Kruskal: runtime output check ── */
  printf("--- Kruskal runtime check ---\n");
  {
    int32_t adj[] = {0,1,3, 1,0,2, 3,2,0};
    size_t edge_u[3] = {0}, edge_v[3] = {0};
    size_t ec = 0;
    CLRS_Ch23_Kruskal_Impl_kruskal(adj, edge_u, edge_v, &ec, (size_t)3);

    CHECK(ec == 2, "edge_count != 2");

    /* MST edges are {(0,1),(1,2)} — any order, any endpoint direction */
    int e0_is_01 = (edge_u[0]==0 && edge_v[0]==1) || (edge_u[0]==1 && edge_v[0]==0);
    int e0_is_12 = (edge_u[0]==1 && edge_v[0]==2) || (edge_u[0]==2 && edge_v[0]==1);
    int e1_is_01 = (edge_u[1]==0 && edge_v[1]==1) || (edge_u[1]==1 && edge_v[1]==0);
    int e1_is_12 = (edge_u[1]==1 && edge_v[1]==2) || (edge_u[1]==2 && edge_v[1]==1);
    CHECK((e0_is_01 && e1_is_12) || (e0_is_12 && e1_is_01),
          "MST edges are not {(0,1),(1,2)}");

    printf("  PASS (ec=%zu, edges={(%zu,%zu),(%zu,%zu)} = MST 0-1-2)\n\n",
           ec, edge_u[0], edge_v[0], edge_u[1], edge_v[1]);
  }

  printf("=== All ch23 tests passed ===\n");
  return 0;
}
