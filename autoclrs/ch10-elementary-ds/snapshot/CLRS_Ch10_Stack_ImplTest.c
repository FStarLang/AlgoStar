/* krml header omitted for test repeatability */


#include "CLRS_Ch10_Stack_ImplTest.h"

bool CLRS_Ch10_Stack_ImplTest_int_eq(krml_checked_int_t a, krml_checked_int_t b)
{
  return a == b;
}

bool CLRS_Ch10_Stack_ImplTest_bool_eq(bool a, bool b)
{
  return a == b;
}

typedef struct stack__krml_checked_int_t_s
{
  krml_checked_int_t *data;
  size_t *top;
}
stack__krml_checked_int_t;

static stack__krml_checked_int_t
create_stack__krml_checked_int_t(krml_checked_int_t default_val, size_t capacity)
{
  KRML_CHECK_SIZE(sizeof (krml_checked_int_t), capacity);
  krml_checked_int_t *arr = KRML_HOST_MALLOC(sizeof (krml_checked_int_t) * capacity);
  if (arr != NULL)
    for (uint32_t _i = 0U; _i < capacity; ++_i)
      arr[_i] = default_val;
  size_t *top_ref = KRML_HOST_CALLOC(1U, sizeof (size_t));
  return ((stack__krml_checked_int_t){ .data = arr, .top = top_ref });
}

static bool stack_empty__krml_checked_int_t(stack__krml_checked_int_t s)
{
  size_t top_val = *s.top;
  return top_val == (size_t)0U;
}

static void push__krml_checked_int_t(stack__krml_checked_int_t s, krml_checked_int_t x)
{
  size_t top_val = *s.top;
  s.data[top_val] = x;
  size_t new_top = top_val + (size_t)1U;
  *s.top = new_top;
}

static krml_checked_int_t peek__krml_checked_int_t(stack__krml_checked_int_t s)
{
  size_t top_val = *s.top;
  size_t idx = top_val - (size_t)1U;
  return s.data[idx];
}

static krml_checked_int_t pop__krml_checked_int_t(stack__krml_checked_int_t s)
{
  size_t top_val = *s.top;
  size_t new_top = top_val - (size_t)1U;
  krml_checked_int_t elem = s.data[new_top];
  *s.top = new_top;
  return elem;
}

bool CLRS_Ch10_Stack_ImplTest_test_stack_spec_validation(void)
{
  stack__krml_checked_int_t
  s = create_stack__krml_checked_int_t((krml_checked_int_t)0, (size_t)5U);
  bool b0 = stack_empty__krml_checked_int_t(s);
  bool pass = b0 == true;
  push__krml_checked_int_t(s, (krml_checked_int_t)1);
  push__krml_checked_int_t(s, (krml_checked_int_t)2);
  push__krml_checked_int_t(s, (krml_checked_int_t)3);
  bool b1 = stack_empty__krml_checked_int_t(s);
  bool pass1 = pass && b1 == false;
  krml_checked_int_t top3 = peek__krml_checked_int_t(s);
  bool pass2 = pass1 && top3 == (krml_checked_int_t)3;
  krml_checked_int_t x3 = pop__krml_checked_int_t(s);
  bool pass3 = pass2 && x3 == (krml_checked_int_t)3;
  krml_checked_int_t top2 = peek__krml_checked_int_t(s);
  bool pass4 = pass3 && top2 == (krml_checked_int_t)2;
  krml_checked_int_t x2 = pop__krml_checked_int_t(s);
  bool pass5 = pass4 && x2 == (krml_checked_int_t)2;
  krml_checked_int_t x1 = pop__krml_checked_int_t(s);
  bool pass6 = pass5 && x1 == (krml_checked_int_t)1;
  bool b2 = stack_empty__krml_checked_int_t(s);
  return pass6 && b2 == true;
}

