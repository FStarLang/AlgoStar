/*
  Minimal support functions for krml-extracted code.
  Provides FStar_SizeT_v, FStar_SizeT_uint_to_t, and any Prims operations
  not supplied by the krmllib runtime.
*/

#include <stdint.h>
#include <stddef.h>
#include "krml/internal/compat.h"

/* FStar.SizeT.v: convert size_t to mathematical integer (int32_t) */
krml_checked_int_t FStar_SizeT_v(size_t x) {
  return (krml_checked_int_t)x;
}

/* FStar.SizeT.uint_to_t: convert mathematical integer to size_t */
size_t FStar_SizeT_uint_to_t(krml_checked_int_t x) {
  return (size_t)x;
}

/* FStar.Int32.to_string: stub */
const char* FStar_Int32_to_string(int32_t i) {
  return "<int>";
}

/* FStar.Pervasives.Native tuple projections for size_t pairs */
typedef struct { size_t fst; size_t snd; } __size_t_size_t;

size_t FStar_Pervasives_Native_fst(__size_t_size_t p) {
  return p.fst;
}

size_t FStar_Pervasives_Native_snd(__size_t_size_t p) {
  return p.snd;
}
