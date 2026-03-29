/* Forward declarations for Prims/FStar runtime stubs (prims_stubs.c). */
#ifndef PRIMS_STUBS_H
#define PRIMS_STUBS_H

#include <stddef.h>
#include <stdbool.h>
#include "krmllib.h"

bool Prims_op_GreaterThanOrEqual(krml_checked_int_t x, krml_checked_int_t y);
bool Prims_op_LessThanOrEqual(krml_checked_int_t x, krml_checked_int_t y);
bool Prims_op_GreaterThan(krml_checked_int_t x, krml_checked_int_t y);
bool Prims_op_LessThan(krml_checked_int_t x, krml_checked_int_t y);
krml_checked_int_t Prims_op_Addition(krml_checked_int_t x, krml_checked_int_t y);
krml_checked_int_t Prims_op_Subtraction(krml_checked_int_t x, krml_checked_int_t y);
krml_checked_int_t Prims_op_Multiply(krml_checked_int_t x, krml_checked_int_t y);
size_t FStar_SizeT_v(size_t x);

#define PRIMS_STUBS_H_DEFINED
#endif /* PRIMS_STUBS_H */
