/* ch22_support.h — Definitions missing from krmllib for Ch22 extraction */
#ifndef CH22_SUPPORT_H
#define CH22_SUPPORT_H

#include <stddef.h>
#include "krml/internal/compat.h"

/* FStar.SizeT.v: extract size_t logical value (identity cast in C) */
static inline krml_checked_int_t FStar_SizeT_v(size_t x) {
  return (krml_checked_int_t)x;
}

/* Prims integer operations — checked arithmetic on krml_checked_int_t */
static inline krml_checked_int_t
Prims_op_Addition(krml_checked_int_t x, krml_checked_int_t y) {
  RETURN_OR((int64_t)x + (int64_t)y);
}

static inline krml_checked_int_t
Prims_op_Subtraction(krml_checked_int_t x, krml_checked_int_t y) {
  RETURN_OR((int64_t)x - (int64_t)y);
}

static inline krml_checked_int_t
Prims_op_Multiply(krml_checked_int_t x, krml_checked_int_t y) {
  RETURN_OR((int64_t)x * (int64_t)y);
}

#endif
