/* krml header omitted for test repeatability */


#ifndef VertexCoverTest_H
#define VertexCoverTest_H

#include "krmllib.h"

#include "krml/internal/compat.h"

bool CLRS_Ch35_VertexCover_ImplTest_test_vertex_cover_triangle(void);

krml_checked_int_t
*CLRS_Ch35_VertexCover_Impl_approx_vertex_cover(krml_checked_int_t *adj, size_t n);


#define VertexCoverTest_H_DEFINED
#endif /* VertexCoverTest_H */
