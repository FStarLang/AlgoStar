/* Compat macros for CLRS Ch26 Max Flow C extraction.
   These provide C implementations for FStar.SizeT conversion functions
   that krml doesn't natively support. */

#ifndef CLRS_CH26_COMPAT_H
#define CLRS_CH26_COMPAT_H

#include <stddef.h>
#include "krml/internal/compat.h"

/* FStar.SizeT.v : SizeT.t -> int (conversion from machine size to math int) */
static inline krml_checked_int_t FStar_SizeT_v(size_t x) {
  return (krml_checked_int_t)x;
}

/* FStar.SizeT.uint_to_t : int -> SizeT.t (conversion from math int to machine size) */
static inline size_t FStar_SizeT_uint_to_t(krml_checked_int_t x) {
  return (size_t)x;
}

#endif /* CLRS_CH26_COMPAT_H */
