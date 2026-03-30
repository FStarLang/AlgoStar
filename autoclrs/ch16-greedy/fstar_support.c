/*
  Minimal support for krml-extracted code.
  Provides functions required by extracted code but not in krmllib.
*/

#include <stddef.h>
#include <stdint.h>

const char* FStar_Int32_to_string(int32_t i) {
  return "<int>";
}

/* FStar.SizeT.v — identity function at extraction (SizeT is size_t) */
size_t FStar_SizeT_v(size_t x) { return x; }
