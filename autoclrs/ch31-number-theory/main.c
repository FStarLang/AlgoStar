#include <stdio.h>
#include "CLRS_Ch31_GCD_ImplTest_CLRS_Ch31_ModExp_ImplTest_CLRS_Ch31_ModExpLR_ImplTest.h"

int main() {
    printf("Ch31 Number Theory Tests\n");
    printf("========================\n");

    printf("Test 1: GCD(12, 8) = 4 ... ");
    CLRS_Ch31_GCD_ImplTest_test_gcd();
    printf("PASSED\n");

    printf("Test 2: 2^10 mod 1000 = 24 ... ");
    CLRS_Ch31_ModExp_ImplTest_test_mod_exp();
    printf("PASSED\n");

    printf("Test 3: 3^5 mod 7 = 5 ... ");
    CLRS_Ch31_ModExpLR_ImplTest_test_mod_exp_lr();
    printf("PASSED\n");

    printf("========================\n");
    printf("All tests passed!\n");
    return 0;
}
