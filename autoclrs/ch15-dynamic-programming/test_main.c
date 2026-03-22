/*
 * Ch15 Dynamic Programming — C test driver
 *
 * Hand-written C implementations that mirror the verified Pulse algorithms.
 * The algorithms are proven correct in F-star/Pulse; this C code is a direct
 * translation of the verified code for concrete execution testing.
 *
 * Each algorithm matches the corresponding Impl.fst exactly:
 *   - Rod Cutting:       bottom-up DP, O(n²)
 *   - LCS:               bottom-up DP table, O(m·n)
 *   - Matrix Chain:      bottom-up DP with 3 nested loops, O(n³)
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ========== Rod Cutting (CLRS §15.1) ========== */

/*
 * Mirrors CLRS.Ch15.RodCutting.Impl.rod_cutting
 * prices: array of n prices (prices[i] = price for piece of length i+1)
 * n: rod length
 * returns: optimal revenue
 */
static int rod_cutting(const int *prices, int n)
{
    int *r = (int *)calloc((size_t)(n + 1), sizeof(int));
    if (!r) { fprintf(stderr, "alloc failed\n"); exit(1); }

    for (int j = 1; j <= n; j++) {
        int q = 0;
        for (int i = 1; i <= j; i++) {
            int candidate = prices[i - 1] + r[j - i];
            if (candidate > q) q = candidate;
        }
        r[j] = q;
    }

    int result = r[n];
    free(r);
    return result;
}

/* ========== LCS (CLRS §15.4) ========== */

/*
 * Mirrors CLRS.Ch15.LCS.Impl.lcs
 * x, y: input arrays
 * m, n: lengths of x and y
 * returns: length of longest common subsequence
 */
static int lcs(const int *x, const int *y, int m, int n)
{
    if (m == 0 || n == 0) return 0;

    int m1 = m + 1;
    int n1 = n + 1;
    int table_size = m1 * n1;
    int *table = (int *)calloc((size_t)table_size, sizeof(int));
    if (!table) { fprintf(stderr, "alloc failed\n"); exit(1); }

    for (int i = 0; i <= m; i++) {
        for (int j = 0; j <= n; j++) {
            int idx = i * n1 + j;
            if (i == 0 || j == 0) {
                table[idx] = 0;
            } else if (x[i - 1] == y[j - 1]) {
                table[idx] = table[(i - 1) * n1 + (j - 1)] + 1;
            } else {
                int up   = table[(i - 1) * n1 + j];
                int left = table[i * n1 + (j - 1)];
                table[idx] = (up >= left) ? up : left;
            }
        }
    }

    int result = table[m * n1 + n];
    free(table);
    return result;
}

/* ========== Matrix Chain (CLRS §15.2) ========== */

/*
 * Mirrors CLRS.Ch15.MatrixChain.Impl.matrix_chain_order
 * dims: array of n+1 dimensions
 * n: number of matrices
 * returns: minimum scalar multiplications
 */
static int matrix_chain_order(const int *dims, int n)
{
    int table_size = n * n;
    int *m_tbl = (int *)calloc((size_t)table_size, sizeof(int));
    if (!m_tbl) { fprintf(stderr, "alloc failed\n"); exit(1); }

    for (int l = 2; l <= n; l++) {
        for (int i = 0; i + l <= n; i++) {
            int j = i + l - 1;
            int min_cost = 1000000000;
            for (int k = i; k < j; k++) {
                int cost_ik  = m_tbl[i * n + k];
                int cost_k1j = m_tbl[(k + 1) * n + j];
                int q = cost_ik + cost_k1j + dims[i] * dims[k + 1] * dims[j + 1];
                if (q < min_cost) min_cost = q;
            }
            m_tbl[i * n + j] = min_cost;
        }
    }

    int result = m_tbl[n - 1]; /* m[0][n-1] */
    free(m_tbl);
    return result;
}

/* ========== Test Driver ========== */

static int test_count = 0;
static int pass_count = 0;

static void check(const char *name, int actual, int expected)
{
    test_count++;
    if (actual == expected) {
        pass_count++;
        printf("  PASS: %s = %d\n", name, actual);
    } else {
        printf("  FAIL: %s = %d (expected %d)\n", name, actual, expected);
    }
}

int main(void)
{
    printf("=== Ch15 Dynamic Programming — Concrete Execution Tests ===\n\n");

    /* --- Rod Cutting (CLRS §15.1) --- */
    printf("Rod Cutting: prices=[1,5,8,9], n=4\n");
    {
        int prices[] = {1, 5, 8, 9};
        int result = rod_cutting(prices, 4);
        check("optimal_revenue", result, 10);
    }

    /* --- LCS (CLRS §15.4) --- */
    printf("\nLCS: x=[1,2,3], y=[2,3,4], m=3, n=3\n");
    {
        int x[] = {1, 2, 3};
        int y[] = {2, 3, 4};
        int result = lcs(x, y, 3, 3);
        check("lcs_length", result, 2);
        check("result >= 0", result >= 0 ? 1 : 0, 1);
        check("result <= m", result <= 3 ? 1 : 0, 1);
        check("result <= n", result <= 3 ? 1 : 0, 1);
    }

    /* --- Matrix Chain (CLRS §15.2) --- */
    printf("\nMatrix Chain: dims=[10,30,5,60], n=3\n");
    {
        int dims[] = {10, 30, 5, 60};
        int result = matrix_chain_order(dims, 3);
        check("mc_result", result, 4500);
        check("result >= 0", result >= 0 ? 1 : 0, 1);
    }

    printf("\n=== Results: %d/%d tests passed ===\n", pass_count, test_count);
    return (pass_count == test_count) ? 0 : 1;
}
