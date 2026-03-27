/*
  Minimal support for krml-extracted code.
  Provides FStar_Int32_to_string required by krmllib prims.c.
*/

#include <stdint.h>

const char* FStar_Int32_to_string(int32_t i) {
  return "<int>";
}

