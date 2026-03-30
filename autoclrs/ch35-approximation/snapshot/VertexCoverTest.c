/* krml header omitted for test repeatability */


#include "VertexCoverTest.h"

bool CLRS_Ch35_VertexCover_ImplTest_test_vertex_cover_triangle(void)
{
  krml_checked_int_t *adj_v = KRML_HOST_CALLOC((size_t)9U, sizeof (krml_checked_int_t));
  krml_checked_int_t *adj = adj_v;
  adj[1U] = (krml_checked_int_t)1;
  adj[2U] = (krml_checked_int_t)1;
  adj[3U] = (krml_checked_int_t)1;
  adj[5U] = (krml_checked_int_t)1;
  adj[6U] = (krml_checked_int_t)1;
  adj[7U] = (krml_checked_int_t)1;
  krml_checked_int_t *cover = CLRS_Ch35_VertexCover_Impl_approx_vertex_cover(adj, (size_t)3U);
  krml_checked_int_t *cover_a = cover;
  krml_checked_int_t c0 = cover_a[0U];
  krml_checked_int_t c1 = cover_a[1U];
  krml_checked_int_t c2 = cover_a[2U];
  bool
  ok =
    c0 == (krml_checked_int_t)1 && c1 == (krml_checked_int_t)1 && c2 == (krml_checked_int_t)0 ||
      c0 == (krml_checked_int_t)1 && c1 == (krml_checked_int_t)0 && c2 == (krml_checked_int_t)1
    || c0 == (krml_checked_int_t)0 && c1 == (krml_checked_int_t)1 && c2 == (krml_checked_int_t)1;
  KRML_HOST_FREE(cover);
  KRML_HOST_FREE(adj_v);
  return ok;
}

krml_checked_int_t
*CLRS_Ch35_VertexCover_Impl_approx_vertex_cover(krml_checked_int_t *adj, size_t n)
{
  KRML_CHECK_SIZE(sizeof (krml_checked_int_t), n);
  krml_checked_int_t *cover = KRML_HOST_CALLOC(n, sizeof (krml_checked_int_t));
  krml_checked_int_t *cover_a = cover;
  size_t u = (size_t)0U;
  size_t __anf00 = u;
  bool cond = __anf00 < n;
  while (cond)
  {
    size_t vu = u;
    size_t v = vu + (size_t)1U;
    size_t __anf0 = v;
    bool cond0 = __anf0 < n;
    while (cond0)
    {
      size_t vv = v;
      size_t u_times_n = vu * n;
      size_t idx = u_times_n + vv;
      krml_checked_int_t cu = cover_a[vu];
      krml_checked_int_t cv = cover_a[vv];
      krml_checked_int_t has_edge = adj[idx];
      krml_checked_int_t new_cu;
      if
      (
        has_edge != (krml_checked_int_t)0 && cu == (krml_checked_int_t)0 &&
          cv == (krml_checked_int_t)0
      )
        new_cu = (krml_checked_int_t)1;
      else
        new_cu = cu;
      krml_checked_int_t new_cv;
      if
      (
        has_edge != (krml_checked_int_t)0 && cu == (krml_checked_int_t)0 &&
          cv == (krml_checked_int_t)0
      )
        new_cv = (krml_checked_int_t)1;
      else
        new_cv = cv;
      cover_a[vu] = new_cu;
      cover_a[vv] = new_cv;
      v = vv + (size_t)1U;
      size_t __anf0 = v;
      cond0 = __anf0 < n;
    }
    u = vu + (size_t)1U;
    size_t __anf00 = u;
    cond = __anf00 < n;
  }
  return cover;
}

