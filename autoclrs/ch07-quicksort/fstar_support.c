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

/* FStar.Int32.to_string: stub for Prims_string_of_int (not used in our tests) */
const char* FStar_Int32_to_string(int32_t i) {
  return "<int>";
}
