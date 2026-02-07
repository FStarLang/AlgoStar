/* Hand-written krmlinit.c
 * Provides proper initialization for Pulse.Lib.BoundedIntegers.bounded_int_int
 * which karamel cannot automatically generate from typeclass lambdas.
 */

#include "krml/internal/compat.h"
#include "krmllib.h"

/* Forward declarations for Prims operations (from karamel krmllib) */
extern krml_checked_int_t Prims_op_Addition(krml_checked_int_t x, krml_checked_int_t y);
extern krml_checked_int_t Prims_op_Subtraction(krml_checked_int_t x, krml_checked_int_t y);
extern bool Prims_op_LessThan(krml_checked_int_t x, krml_checked_int_t y);
extern bool Prims_op_LessThanOrEqual(krml_checked_int_t x, krml_checked_int_t y);
extern bool Prims_op_GreaterThan(krml_checked_int_t x, krml_checked_int_t y);
extern bool Prims_op_GreaterThanOrEqual(krml_checked_int_t x, krml_checked_int_t y);
extern krml_checked_int_t Prims_op_Modulus(krml_checked_int_t x, krml_checked_int_t y);
extern krml_checked_int_t Prims_op_Division(krml_checked_int_t x, krml_checked_int_t y);

/* The BoundedIntegers typeclass struct (must match karamel's generated layout) */
typedef struct Pulse_Lib_BoundedIntegers_bounded_int__krml_checked_int_t_s {
    krml_checked_int_t (*op_Plus)(krml_checked_int_t, krml_checked_int_t);
    krml_checked_int_t (*op_Subtraction)(krml_checked_int_t, krml_checked_int_t);
    bool (*op_Less)(krml_checked_int_t, krml_checked_int_t);
    bool (*op_Less_Equals)(krml_checked_int_t, krml_checked_int_t);
    bool (*op_Greater)(krml_checked_int_t, krml_checked_int_t);
    bool (*op_Greater_Equals)(krml_checked_int_t, krml_checked_int_t);
    krml_checked_int_t (*op_Percent)(krml_checked_int_t, krml_checked_int_t);
    krml_checked_int_t (*op_Slash)(krml_checked_int_t, krml_checked_int_t);
} Pulse_Lib_BoundedIntegers_bounded_int__krml_checked_int_t;

/* Global instances used by extracted code */
Pulse_Lib_BoundedIntegers_bounded_int__krml_checked_int_t
Pulse_Lib_BoundedIntegers_bounded_int_int;

Pulse_Lib_BoundedIntegers_bounded_int__krml_checked_int_t
Pulse_Lib_BoundedIntegers_bounded_int_nat;

/* FStar_SizeT conversions (used by extracted code) */
size_t FStar_SizeT_uint_to_t(krml_checked_int_t x) {
    return (size_t)x;
}

krml_checked_int_t FStar_SizeT_v(size_t x) {
    return (krml_checked_int_t)x;
}

/* FStar_Char conversion (used by RabinKarp) */
krml_checked_int_t FStar_Char_int_of_char(FStar_Char_char c) {
    return (krml_checked_int_t)c;
}

/* FStar_Char equality (used by RabinKarp) */
bool __eq__FStar_Char_char(FStar_Char_char x, FStar_Char_char y) {
    return x == y;
}

void krmlinit_globals(void) {
    Pulse_Lib_BoundedIntegers_bounded_int_int.op_Plus = Prims_op_Addition;
    Pulse_Lib_BoundedIntegers_bounded_int_int.op_Subtraction = Prims_op_Subtraction;
    Pulse_Lib_BoundedIntegers_bounded_int_int.op_Less = Prims_op_LessThan;
    Pulse_Lib_BoundedIntegers_bounded_int_int.op_Less_Equals = Prims_op_LessThanOrEqual;
    Pulse_Lib_BoundedIntegers_bounded_int_int.op_Greater = Prims_op_GreaterThan;
    Pulse_Lib_BoundedIntegers_bounded_int_int.op_Greater_Equals = Prims_op_GreaterThanOrEqual;
    Pulse_Lib_BoundedIntegers_bounded_int_int.op_Percent = Prims_op_Modulus;
    Pulse_Lib_BoundedIntegers_bounded_int_int.op_Slash = Prims_op_Division;

    /* bounded_int_nat is the same as bounded_int_int */
    Pulse_Lib_BoundedIntegers_bounded_int_nat = Pulse_Lib_BoundedIntegers_bounded_int_int;
}
