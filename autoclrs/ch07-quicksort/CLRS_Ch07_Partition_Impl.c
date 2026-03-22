/*
  Hand-written C implementation of CLRS Lomuto partition.

  This corresponds to CLRS.Ch07.Partition.Impl.clrs_partition_wrapper_with_ticks
  after krml extraction (ghost parameters erased).

  The krml extraction of all three modules together triggers a bug in
  karamel's remove_unused_parameters pass, so we provide the partition
  implementation separately. The function signature matches exactly what
  krml generates for the caller (CLRS_Ch07_Quicksort_Impl.c).
*/

#include "internal/CLRS_Ch07_Partition_Impl.h"

/* Lomuto partition: pivot = a[hi-1], rearrange a[lo..hi) so that
   elements <= pivot come before the pivot position, elements > pivot after.
   Returns the final index of the pivot. */
krml_checked_int_t
CLRS_Ch07_Partition_Impl_clrs_partition_wrapper_with_ticks(
  krml_checked_int_t *a,
  krml_checked_int_t lo,
  krml_checked_int_t hi)
{
  krml_checked_int_t pivot = a[hi - 1];
  krml_checked_int_t i = lo;
  for (krml_checked_int_t j = lo; j < hi - 1; j++) {
    if (a[j] <= pivot) {
      krml_checked_int_t tmp = a[i];
      a[i] = a[j];
      a[j] = tmp;
      i++;
    }
  }
  /* swap a[i] and a[hi-1] (place pivot in final position) */
  krml_checked_int_t tmp = a[i];
  a[i] = a[hi - 1];
  a[hi - 1] = tmp;
  return i;
}
