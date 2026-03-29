/* Minimal Prims shim for CLRS Ch33 extracted C code.
 * Provides only the Prims_op_* functions actually referenced. */

#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include "krml/internal/target.h"
#include "krml/internal/compat.h"

int32_t Prims_op_Multiply(int32_t x, int32_t y) { RETURN_OR((int64_t)x * (int64_t)y); }
int32_t Prims_op_Subtraction(int32_t x, int32_t y) { RETURN_OR((int64_t)x - (int64_t)y); }
bool Prims_op_GreaterThanOrEqual(int32_t x, int32_t y) { return x >= y; }
bool Prims_op_LessThanOrEqual(int32_t x, int32_t y) { return x <= y; }
bool Prims_op_GreaterThan(int32_t x, int32_t y) { return x > y; }
bool Prims_op_LessThan(int32_t x, int32_t y) { return x < y; }
