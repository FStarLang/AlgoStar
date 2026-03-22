/* Forward declarations for hand-written hash table C implementations */
#ifndef CLRS_Ch11_HashTable_Impl_H
#define CLRS_Ch11_HashTable_Impl_H

#include "krmllib.h"
#include "krml/internal/compat.h"

krml_checked_int_t *CLRS_Ch11_HashTable_Impl_hash_table_create(size_t size);

void CLRS_Ch11_HashTable_Impl_hash_table_free(
    krml_checked_int_t *tv, void *s_erased);

bool CLRS_Ch11_HashTable_Impl_hash_insert(
    krml_checked_int_t *table, void *s_erased,
    size_t size, krml_checked_int_t key,
    void *ctr_erased, void *c0_erased);

size_t CLRS_Ch11_HashTable_Impl_hash_search(
    krml_checked_int_t *table, void *s_erased,
    size_t size, krml_checked_int_t key,
    void *ctr_erased, void *c0_erased);

bool CLRS_Ch11_HashTable_Impl_hash_delete(
    krml_checked_int_t *table, void *s_erased,
    size_t size, krml_checked_int_t key,
    void *ctr_erased, void *c0_erased);

bool CLRS_Ch11_HashTable_Impl_hash_insert_no_dup(
    krml_checked_int_t *table, void *s_erased,
    size_t size, krml_checked_int_t key,
    void *ctr_erased, void *c0_erased);

#endif /* CLRS_Ch11_HashTable_Impl_H */
