/* Compatibility shims for CLRS Ch26 Max Flow C extraction.
   
   These provide C implementations for FStar.SizeT conversion functions
   that KaRaMeL doesn't natively support. They appear in the extracted
   code because the Impl stores predecessor indices as `int` (using -1
   as sentinel for "no predecessor") while vertex indices are `size_t`.
   
   The F* proofs guarantee these conversions are safe:
   - FStar_SizeT_v: only called on valid vertex indices (< n)
   - FStar_SizeT_uint_to_t: only called on values read from pred[]
     that are proven to be valid vertex indices (>= 0 and < n)
   
   Eliminating this header would require refactoring the pred array
   to use size_t with a sentinel value instead of int with -1. */

#ifndef CLRS_CH26_COMPAT_H
#define CLRS_CH26_COMPAT_H

#include <stddef.h>
#include <assert.h>
#include "krml/internal/compat.h"

/* FStar.SizeT.v : SizeT.t -> int (vertex index to math int) */
static inline krml_checked_int_t FStar_SizeT_v(size_t x) {
  assert(x <= (size_t)__INT_MAX__);
  return (krml_checked_int_t)x;
}

/* FStar.SizeT.uint_to_t : int -> SizeT.t (math int to vertex index) */
static inline size_t FStar_SizeT_uint_to_t(krml_checked_int_t x) {
  assert(x >= 0);
  return (size_t)x;
}

#endif /* CLRS_CH26_COMPAT_H */
