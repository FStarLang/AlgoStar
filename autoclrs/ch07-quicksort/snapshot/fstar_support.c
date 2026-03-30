/*
  *** HANDWRITTEN FILE — NOT GENERATED ***

  Trusted shims for FStar.SizeT operations used in extracted code.

  The Pulse implementation uses nat (extracted to krml_checked_int_t) for
  array index arithmetic (lo, hi, p) but FStar.SizeT.t (size_t) for
  array lengths and the top-level API. The extracted C code calls
  FStar_SizeT_v and FStar_SizeT_uint_to_t to convert between these types.

  These shims are in the trusted computing base: the casts are safe because
  all values are small non-negative integers (array indices bounded by length).
  A future improvement would be to extract FStar.SizeT as a .krml and have
  KaRaMeL generate these automatically.
*/

#include <stdint.h>
#include <stddef.h>
#include "krml/internal/compat.h"

/* FStar.SizeT.v: size_t → krml_checked_int_t (mathematical integer) */
krml_checked_int_t FStar_SizeT_v(size_t x) {
  return (krml_checked_int_t)x;
}

/* FStar.SizeT.uint_to_t: krml_checked_int_t → size_t */
size_t FStar_SizeT_uint_to_t(krml_checked_int_t x) {
  return (size_t)x;
}

/* Stub required by prims.c (Prims_string_of_int calls FStar_Int32_to_string).
   Not used in our test code; only needed to satisfy the linker. */
const char* FStar_Int32_to_string(int32_t i) {
  (void)i;
  return "<int>";
}
