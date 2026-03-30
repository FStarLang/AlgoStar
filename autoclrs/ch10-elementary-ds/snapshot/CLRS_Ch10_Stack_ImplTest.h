/* krml header omitted for test repeatability */


#ifndef CLRS_Ch10_Stack_ImplTest_H
#define CLRS_Ch10_Stack_ImplTest_H

#include "krmllib.h"

#include "krml/internal/compat.h"

bool CLRS_Ch10_Stack_ImplTest_int_eq(krml_checked_int_t a, krml_checked_int_t b);

bool CLRS_Ch10_Stack_ImplTest_bool_eq(bool a, bool b);

bool CLRS_Ch10_Stack_ImplTest_test_stack_spec_validation(void);


#define CLRS_Ch10_Stack_ImplTest_H_DEFINED
#endif /* CLRS_Ch10_Stack_ImplTest_H */
