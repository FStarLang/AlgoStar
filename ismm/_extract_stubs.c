/*
 * Stubs for KaRaMeL-extracted ISMM code.
 * Provides main() wrapper and runtime helpers.
 */

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>

/* eprintf helper for KRML_HOST_EPRINTF */
int eprintf_helper(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    int r = vfprintf(stderr, fmt, args);
    va_end(args);
    return r;
}

/* Forward-declare the extracted test function */
void test_uf(void);

int main(void) {
    printf("=== ISMM Extracted C Test ===\n");
    test_uf();
    printf("=== Test passed ===\n");
    return 0;
}
