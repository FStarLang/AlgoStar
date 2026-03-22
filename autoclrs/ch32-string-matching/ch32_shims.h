/* Shims for symbols not provided by krmllib */
#ifndef CH32_SHIMS_H
#define CH32_SHIMS_H

#include <stddef.h>
#include "krml/internal/compat.h"

static inline krml_checked_int_t FStar_SizeT_v(size_t x) {
  return (krml_checked_int_t)x;
}

#endif
