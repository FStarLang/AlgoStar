/*
 * Stubs for KaRaMeL-extracted ISMM code.
 * Provides main() wrapper and runtime helpers needed by krmllib.
 */

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

/* eprintf helper for KRML_HOST_EPRINTF */
int eprintf_helper(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    int r = vfprintf(stderr, fmt, args);
    va_end(args);
    return r;
}

/* Prims checked-integer arithmetic (from krmllib/c/prims.c) */
#define RETURN_OR(x) do { \
    int64_t __ret = (x); \
    if (__ret < INT32_MIN || INT32_MAX < __ret) { \
      fprintf(stderr, "Prims integer overflow at %s:%d\n", __FILE__, __LINE__); \
      exit(252); \
    } \
    return (int32_t)__ret; \
  } while (0)

int32_t Prims_op_Addition(int32_t x, int32_t y)    { RETURN_OR((int64_t)x + (int64_t)y); }
int32_t Prims_op_Subtraction(int32_t x, int32_t y) { RETURN_OR((int64_t)x - (int64_t)y); }
int32_t Prims_op_Multiply(int32_t x, int32_t y)    { RETURN_OR((int64_t)x * (int64_t)y); }
int32_t Prims_op_Division(int32_t x, int32_t y)    { RETURN_OR((int64_t)x / (int64_t)y); }
int32_t Prims_op_Modulus(int32_t x, int32_t y)     { RETURN_OR((int64_t)x % (int64_t)y); }
int32_t Prims_op_Minus(int32_t x)                  { RETURN_OR(-(int64_t)x); }

/* FStar.SizeT.ne — size_t inequality */
bool FStar_SizeT_ne(size_t a, size_t b) { return a != b; }

/* Forward-declare the extracted test function */
void test_uf(void);

int main(void) {
    printf("=== ISMM Extracted C Test ===\n");
    test_uf();
    printf("=== Test passed ===\n");
    return 0;
}
