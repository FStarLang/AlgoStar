/* Compatibility shim: F*2 extracts Prims.op_Star for integer multiplication,
   but the krmllib runtime defines it as Prims_op_Multiply. */

#include "krml/internal/compat.h"
#include "Prims.h"

krml_checked_int_t Prims_op_Star(krml_checked_int_t x, krml_checked_int_t y) {
  return x * y;
}
