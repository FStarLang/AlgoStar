/* ============================================================
 * HANDWRITTEN — Minimal Prims runtime for CLRS Ch26 snapshot
 * ============================================================
 *
 * This file provides the small subset of KaRaMeL's Prims runtime
 * (checked-integer arithmetic) that the extracted Max Flow code
 * actually uses.  It replaces the full krmllib/dist/generic/prims.c
 * to keep the snapshot dependency-free.
 *
 * Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
 * Licensed under the Apache 2.0 and MIT Licenses.
 */

#include <stdbool.h>
#include <stdint.h>
#include "krml/internal/target.h"
#include "krml/internal/compat.h"

int32_t Prims_op_Addition(int32_t x, int32_t y) {
  RETURN_OR((int64_t)x + (int64_t)y);
}

int32_t Prims_op_Subtraction(int32_t x, int32_t y) {
  RETURN_OR((int64_t)x - (int64_t)y);
}

bool Prims_op_GreaterThan(int32_t x, int32_t y) {
  return x > y;
}

bool Prims_op_GreaterThanOrEqual(int32_t x, int32_t y) {
  return x >= y;
}

bool Prims_op_LessThan(int32_t x, int32_t y) {
  return x < y;
}
