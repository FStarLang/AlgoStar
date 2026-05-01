/* Shims for symbols not provided by krmllib */
#ifndef CH32_SHIMS_H
#define CH32_SHIMS_H

#include <stddef.h>
#include "krml/internal/compat.h"
#include "Prims.h"

/* F* nightly (2026.03.24+) extracts op_Star; krmllib still uses op_Multiply */
#define Prims_op_Star Prims_op_Multiply

static inline krml_checked_int_t FStar_SizeT_v(size_t x) {
  return (krml_checked_int_t)x;
}

/* FStar.List.Tot.Base.length and .index are used polymorphically by
   KaRaMeL-generated wrappers.  Implement them as type-generic macros
   using GCC statement expressions so that they work for every
   Prims_list__<T> monomorphisation (all share .tag / .hd / .tl). */
#define FStar_List_Tot_Base_length(s) \
  __extension__({ \
    __typeof__(s) _lst = (s); \
    krml_checked_int_t _len = 0; \
    while (_lst->tag != 0) { _lst = _lst->tl; _len++; } \
    _len; \
  })

#define FStar_List_Tot_Base_index(s, i) \
  __extension__({ \
    __typeof__(s) _lst2 = (s); \
    krml_checked_int_t _idx = (i); \
    while (_idx > 0) { _lst2 = _lst2->tl; _idx--; } \
    _lst2->hd; \
  })

#endif
