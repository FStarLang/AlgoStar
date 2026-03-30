/* krml header omitted for test repeatability */


#ifndef internal_Prims_H
#define internal_Prims_H

#include "krmllib.h"

#include "krml/internal/compat.h"

extern krml_checked_int_t Prims_op_Multiply(krml_checked_int_t x, krml_checked_int_t y);

extern krml_checked_int_t Prims_op_Addition(krml_checked_int_t x, krml_checked_int_t y);

extern bool Prims_op_GreaterThan(krml_checked_int_t x0, krml_checked_int_t x1);

extern bool Prims_op_LessThan(krml_checked_int_t x0, krml_checked_int_t x1);


#define internal_Prims_H_DEFINED
#endif /* internal_Prims_H */
