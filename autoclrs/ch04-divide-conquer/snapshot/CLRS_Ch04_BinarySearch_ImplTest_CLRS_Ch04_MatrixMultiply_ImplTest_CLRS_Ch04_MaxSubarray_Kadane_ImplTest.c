/* krml header omitted for test repeatability */


#include "CLRS_Ch04_BinarySearch_ImplTest_CLRS_Ch04_MatrixMultiply_ImplTest_CLRS_Ch04_MaxSubarray_Kadane_ImplTest.h"

#include "internal/FStar_Pulse_PulseCore_Prims.h"

static size_t binary_search(krml_checked_int_t *a, size_t len, krml_checked_int_t key)
{
  if (len == (size_t)0U)
    return len;
  else
  {
    size_t lo = (size_t)0U;
    size_t hi = len;
    bool found = false;
    size_t result_idx = len;
    size_t __anf2 = lo;
    size_t __anf10 = hi;
    bool __anf00 = found;
    bool cond = __anf2 < __anf10 && !__anf00;
    while (cond)
    {
      size_t vlo = lo;
      size_t vhi = hi;
      size_t diff = vhi - vlo;
      size_t half = diff / (size_t)2U;
      size_t mid = vlo + half;
      krml_checked_int_t mid_val = a[mid];
      if (mid_val == key)
      {
        found = true;
        result_idx = mid;
      }
      else if (Prims_op_LessThan(mid_val, key))
        lo = mid + (size_t)1U;
      else
        hi = mid;
      size_t __anf2 = lo;
      size_t __anf1 = hi;
      bool __anf0 = found;
      cond = __anf2 < __anf1 && !__anf0;
    }
    return result_idx;
  }
}

static void
matrix_multiply(krml_checked_int_t *a, krml_checked_int_t *b, krml_checked_int_t *c, size_t n)
{
  size_t i = (size_t)0U;
  size_t __anf00 = i;
  bool cond = __anf00 < n;
  while (cond)
  {
    size_t vi = i;
    size_t j = (size_t)0U;
    size_t __anf00 = j;
    bool cond0 = __anf00 < n;
    while (cond0)
    {
      size_t vj = j;
      size_t idx_c = vi * n + vj;
      c[idx_c] = (krml_checked_int_t)0;
      size_t k = (size_t)0U;
      size_t __anf0 = k;
      bool cond = __anf0 < n;
      while (cond)
      {
        size_t vk = k;
        size_t idx_a = vi * n + vk;
        size_t idx_b = vk * n + vj;
        krml_checked_int_t a_val = a[idx_a];
        krml_checked_int_t b_val = b[idx_b];
        krml_checked_int_t c_val = c[idx_c];
        krml_checked_int_t new_val = Prims_op_Addition(c_val, Prims_op_Multiply(a_val, b_val));
        c[idx_c] = new_val;
        k = vk + (size_t)1U;
        size_t __anf0 = k;
        cond = __anf0 < n;
      }
      j = vj + (size_t)1U;
      size_t __anf00 = j;
      cond0 = __anf00 < n;
    }
    i = vi + (size_t)1U;
    size_t __anf0 = i;
    cond = __anf0 < n;
  }
}

static krml_checked_int_t max_subarray(krml_checked_int_t *a, size_t len)
{
  krml_checked_int_t first_elem = a[0U];
  krml_checked_int_t current_sum = (krml_checked_int_t)0;
  krml_checked_int_t best_sum = first_elem;
  size_t i = (size_t)0U;
  size_t __anf0 = i;
  bool cond = __anf0 < len;
  while (cond)
  {
    size_t vi = i;
    krml_checked_int_t vcur = current_sum;
    krml_checked_int_t vbest = best_sum;
    krml_checked_int_t elem = a[vi];
    krml_checked_int_t sum_with_current = Prims_op_Addition(vcur, elem);
    krml_checked_int_t new_current = elem;
    if (Prims_op_GreaterThan(sum_with_current, elem))
      new_current = sum_with_current;
    krml_checked_int_t vnew_current = new_current;
    krml_checked_int_t new_best = vbest;
    if (Prims_op_GreaterThan(vnew_current, vbest))
      new_best = vnew_current;
    krml_checked_int_t vnew_best = new_best;
    current_sum = vnew_current;
    best_sum = vnew_best;
    i = vi + (size_t)1U;
    size_t __anf0 = i;
    cond = __anf0 < len;
  }
  return best_sum;
}

bool CLRS_Ch04_BinarySearch_ImplTest_sz_eq(size_t a, size_t b)
{
  return !(a < b || b < a);
}

bool CLRS_Ch04_BinarySearch_ImplTest_test_binary_search_found(void)
{
  krml_checked_int_t *v = KRML_HOST_CALLOC((size_t)3U, sizeof (krml_checked_int_t));
  krml_checked_int_t *arr = v;
  arr[0U] = (krml_checked_int_t)1;
  arr[1U] = (krml_checked_int_t)3;
  arr[2U] = (krml_checked_int_t)5;
  size_t result = binary_search(arr, (size_t)3U, (krml_checked_int_t)3);
  bool ok = !(result < (size_t)1U || (size_t)1U < result);
  KRML_HOST_FREE(v);
  return ok;
}

bool CLRS_Ch04_BinarySearch_ImplTest_test_binary_search_not_found(void)
{
  krml_checked_int_t *v = KRML_HOST_CALLOC((size_t)3U, sizeof (krml_checked_int_t));
  krml_checked_int_t *arr = v;
  arr[0U] = (krml_checked_int_t)1;
  arr[1U] = (krml_checked_int_t)3;
  arr[2U] = (krml_checked_int_t)5;
  size_t result = binary_search(arr, (size_t)3U, (krml_checked_int_t)2);
  bool ok = !(result < (size_t)3U || (size_t)3U < result);
  KRML_HOST_FREE(v);
  return ok;
}

bool CLRS_Ch04_BinarySearch_ImplTest_test_binary_search_empty(void)
{
  krml_checked_int_t *v = KRML_HOST_CALLOC((size_t)0U, sizeof (krml_checked_int_t));
  krml_checked_int_t *arr = v;
  size_t result = binary_search(arr, (size_t)0U, (krml_checked_int_t)1);
  bool ok = !(result < (size_t)0U || (size_t)0U < result);
  KRML_HOST_FREE(v);
  return ok;
}

bool CLRS_Ch04_MatrixMultiply_ImplTest_test_matrix_multiply_2x2(void)
{
  krml_checked_int_t *av = KRML_HOST_CALLOC((size_t)4U, sizeof (krml_checked_int_t));
  krml_checked_int_t *a_arr = av;
  a_arr[0U] = (krml_checked_int_t)1;
  a_arr[1U] = (krml_checked_int_t)2;
  a_arr[2U] = (krml_checked_int_t)3;
  a_arr[3U] = (krml_checked_int_t)4;
  krml_checked_int_t *bv = KRML_HOST_CALLOC((size_t)4U, sizeof (krml_checked_int_t));
  krml_checked_int_t *b_arr = bv;
  b_arr[0U] = (krml_checked_int_t)5;
  b_arr[1U] = (krml_checked_int_t)6;
  b_arr[2U] = (krml_checked_int_t)7;
  b_arr[3U] = (krml_checked_int_t)8;
  krml_checked_int_t *cv = KRML_HOST_CALLOC((size_t)4U, sizeof (krml_checked_int_t));
  krml_checked_int_t *c_arr = cv;
  matrix_multiply(a_arr, b_arr, c_arr, (size_t)2U);
  krml_checked_int_t c00 = c_arr[0U];
  krml_checked_int_t c01 = c_arr[1U];
  krml_checked_int_t c10 = c_arr[2U];
  krml_checked_int_t c11 = c_arr[3U];
  bool
  ok =
    c00 == (krml_checked_int_t)19 && c01 == (krml_checked_int_t)22 && c10 == (krml_checked_int_t)43
    && c11 == (krml_checked_int_t)50;
  KRML_HOST_FREE(cv);
  KRML_HOST_FREE(bv);
  KRML_HOST_FREE(av);
  return ok;
}

bool CLRS_Ch04_MaxSubarray_Kadane_ImplTest_test_kadane_max_subarray(void)
{
  krml_checked_int_t *v = KRML_HOST_CALLOC((size_t)3U, sizeof (krml_checked_int_t));
  krml_checked_int_t *arr = v;
  arr[0U] = (krml_checked_int_t)-1;
  arr[1U] = (krml_checked_int_t)3;
  arr[2U] = (krml_checked_int_t)-2;
  krml_checked_int_t result = max_subarray(arr, (size_t)3U);
  bool ok = result == (krml_checked_int_t)3;
  KRML_HOST_FREE(v);
  return ok;
}

bool CLRS_Ch04_MaxSubarray_Kadane_ImplTest_test_kadane_all_negative(void)
{
  krml_checked_int_t *v = KRML_HOST_CALLOC((size_t)3U, sizeof (krml_checked_int_t));
  krml_checked_int_t *arr = v;
  arr[0U] = (krml_checked_int_t)-5;
  arr[1U] = (krml_checked_int_t)-3;
  arr[2U] = (krml_checked_int_t)-1;
  krml_checked_int_t result = max_subarray(arr, (size_t)3U);
  bool ok = result == (krml_checked_int_t)-1;
  KRML_HOST_FREE(v);
  return ok;
}

