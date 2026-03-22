/* Shim for FStar.SizeT conversions used in extracted C code */
#ifndef FSTAR_SIZET_SHIM_H
#define FSTAR_SIZET_SHIM_H

#include "krmllib.h"

static inline size_t FStar_SizeT_uint_to_t(krml_checked_int_t x) {
  return (size_t)x;
}

static inline krml_checked_int_t FStar_SizeT_v(size_t x) {
  return (krml_checked_int_t)x;
}

#endif
