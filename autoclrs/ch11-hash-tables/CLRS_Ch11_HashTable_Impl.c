/*
  C implementation of hash table operations from CLRS Ch11.
  These match the verified Pulse implementations in CLRS.Ch11.HashTable.Impl.fst.

  Division-method hash: h(k) = k % size
  Linear probing: h(k, i) = (h(k) + i) % size
  Sentinel values: -1 = empty, -2 = deleted, >= 0 = valid key

  Signatures match the KaRaMeL-extracted externs (erased params removed).
*/

#include "CLRS_Ch11_HashTable_Impl.h"

static size_t hash_probe(krml_checked_int_t key, size_t i, size_t size) {
  return (size_t)(((size_t)(key % (krml_checked_int_t)size) + i) % size);
}

krml_checked_int_t *CLRS_Ch11_HashTable_Impl_hash_table_create(size_t size) {
  krml_checked_int_t *table =
      (krml_checked_int_t *)KRML_HOST_MALLOC(sizeof(krml_checked_int_t) * size);
  for (size_t j = 0; j < size; j++)
    table[j] = -1;
  return table;
}

void CLRS_Ch11_HashTable_Impl_hash_table_free(krml_checked_int_t *tv) {
  KRML_HOST_FREE(tv);
}

bool CLRS_Ch11_HashTable_Impl_hash_insert(
    krml_checked_int_t *table, size_t size, krml_checked_int_t key) {
  for (size_t i = 0; i < size; i++) {
    size_t idx = hash_probe(key, i, size);
    krml_checked_int_t slot = table[idx];
    if (slot == -1 || slot == -2) {
      table[idx] = key;
      return true;
    }
  }
  return false;
}

size_t CLRS_Ch11_HashTable_Impl_hash_search(
    krml_checked_int_t *table, size_t size, krml_checked_int_t key) {
  for (size_t i = 0; i < size; i++) {
    size_t idx = hash_probe(key, i, size);
    krml_checked_int_t slot = table[idx];
    if (slot == key)
      return idx;
    if (slot == -1)
      return size;
  }
  return size;
}

bool CLRS_Ch11_HashTable_Impl_hash_delete(
    krml_checked_int_t *table, size_t size, krml_checked_int_t key) {
  size_t r = CLRS_Ch11_HashTable_Impl_hash_search(table, size, key);
  if (r < size) {
    table[r] = -2;
    return true;
  }
  return false;
}

bool CLRS_Ch11_HashTable_Impl_hash_insert_no_dup(
    krml_checked_int_t *table, size_t size, krml_checked_int_t key) {
  size_t r = CLRS_Ch11_HashTable_Impl_hash_search(table, size, key);
  if (r < size)
    return true;
  return CLRS_Ch11_HashTable_Impl_hash_insert(table, size, key);
}
