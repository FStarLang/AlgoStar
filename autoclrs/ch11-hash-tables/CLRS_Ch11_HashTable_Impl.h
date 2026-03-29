/* Forward declarations for hand-written hash table C implementations.
   Signatures match the KaRaMeL-extracted externs (erased params removed). */
#ifndef CLRS_Ch11_HashTable_Impl_H
#define CLRS_Ch11_HashTable_Impl_H

#include "krmllib.h"
#include "krml/internal/compat.h"

krml_checked_int_t *CLRS_Ch11_HashTable_Impl_hash_table_create(size_t size);

void CLRS_Ch11_HashTable_Impl_hash_table_free(krml_checked_int_t *tv);

bool CLRS_Ch11_HashTable_Impl_hash_insert(
    krml_checked_int_t *table, size_t size, krml_checked_int_t key);

size_t CLRS_Ch11_HashTable_Impl_hash_search(
    krml_checked_int_t *table, size_t size, krml_checked_int_t key);

bool CLRS_Ch11_HashTable_Impl_hash_delete(
    krml_checked_int_t *table, size_t size, krml_checked_int_t key);

bool CLRS_Ch11_HashTable_Impl_hash_insert_no_dup(
    krml_checked_int_t *table, size_t size, krml_checked_int_t key);

#endif /* CLRS_Ch11_HashTable_Impl_H */
