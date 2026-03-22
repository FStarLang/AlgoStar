/* Test driver for verified SSSP algorithms (Ch24)
 *
 * Calls the extracted Bellman-Ford and Dijkstra implementations on
 * small concrete graphs and checks the computed shortest distances.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "Ch24_SSSP.h"
#include "krmlinit.h"

#define INF 1000000

static int test_bellman_ford(void) {
    /* 3-vertex graph:
     *   0→1: 4, 0→2: 5, 1→2: -2
     * Expected: dist = [0, 4, 2], no_neg_cycle = true */
    krml_checked_int_t weights[9] = {
        INF, 4, 5,
        INF, INF, -2,
        INF, INF, INF
    };
    krml_checked_int_t dist[3] = {0, 0, 0};
    bool no_neg_cycle = false;

    bellman_ford0(weights, 3, 0, dist, &no_neg_cycle);

    printf("Bellman-Ford (3 vertices, source=0):\n");
    printf("  dist = [%d, %d, %d]\n", dist[0], dist[1], dist[2]);
    printf("  no_neg_cycle = %s\n", no_neg_cycle ? "true" : "false");

    int ok = (dist[0] == 0 && dist[1] == 4 && dist[2] == 2 && no_neg_cycle);
    printf("  result: %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

static int test_dijkstra(void) {
    /* 3-vertex graph:
     *   0→1: 3, 0→2: 7, 1→2: 2
     * Expected: dist = [0, 3, 5] */
    krml_checked_int_t weights[9] = {
        INF, 3, 7,
        INF, INF, 2,
        INF, INF, INF
    };
    krml_checked_int_t dist[3] = {0, 0, 0};
    size_t pred[3] = {0, 0, 0};

    dijkstra1(weights, 3, 0, dist, pred);

    printf("Dijkstra (3 vertices, source=0):\n");
    printf("  dist = [%d, %d, %d]\n", dist[0], dist[1], dist[2]);
    printf("  pred = [%zu, %zu, %zu]\n", pred[0], pred[1], pred[2]);

    int ok = (dist[0] == 0 && dist[1] == 3 && dist[2] == 5);
    printf("  result: %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}

int main(void) {
    krmlinit_globals();

    int rc = 0;
    rc |= test_bellman_ford();
    rc |= test_dijkstra();

    if (rc == 0)
        printf("\nAll tests PASSED\n");
    else
        printf("\nSome tests FAILED\n");

    return rc;
}
