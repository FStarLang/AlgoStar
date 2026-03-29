/* Stubs for Prims and FStar runtime functions needed by extracted C code. */
#include "prims_stubs.h"

bool Prims_op_GreaterThanOrEqual(krml_checked_int_t x, krml_checked_int_t y) { return x >= y; }
bool Prims_op_LessThanOrEqual(krml_checked_int_t x, krml_checked_int_t y) { return x <= y; }
bool Prims_op_GreaterThan(krml_checked_int_t x, krml_checked_int_t y) { return x > y; }
bool Prims_op_LessThan(krml_checked_int_t x, krml_checked_int_t y) { return x < y; }
krml_checked_int_t Prims_op_Addition(krml_checked_int_t x, krml_checked_int_t y) { return x + y; }
krml_checked_int_t Prims_op_Subtraction(krml_checked_int_t x, krml_checked_int_t y) { return x - y; }
krml_checked_int_t Prims_op_Multiply(krml_checked_int_t x, krml_checked_int_t y) { return x * y; }
size_t FStar_SizeT_v(size_t x) { return x; }
