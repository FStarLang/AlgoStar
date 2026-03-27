/*
  Support functions for krml-extracted code.
  
  FStar_SizeT_v: should not appear in extracted code (spec function),
  but Kruskal.Impl uses SZ.v in computational position (known issue).
  
  Tuple projections: KaRaMeL doesn't monomorphize FStar.Pervasives.Native
  tuple types for Prim's (vec & vec) return type.
*/

#include <stdint.h>
#include <stddef.h>
#include "krml/internal/compat.h"

/* FStar.SizeT.v — spec function leaking into Kruskal extraction */
krml_checked_int_t FStar_SizeT_v(size_t x) {
  return (krml_checked_int_t)x;
}

/* FStar.SizeT.uint_to_t */
size_t FStar_SizeT_uint_to_t(krml_checked_int_t x) {
  return (size_t)x;
}

/* Tuple projections for (size_t*, size_t*) pairs */
typedef struct { size_t *fst; size_t *snd; } __size_t___size_t_;

size_t *FStar_Pervasives_Native_fst(__size_t___size_t_ p) {
  return p.fst;
}

size_t *FStar_Pervasives_Native_snd(__size_t___size_t_ p) {
  return p.snd;
}

/* Required by krmllib prims.c */
const char* FStar_Int32_to_string(int32_t i) { return "<int>"; }

