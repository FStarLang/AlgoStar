# CLRS Chapter 11: Hash Tables with Linear Probing

This directory contains a verified Pulse implementation of a hash table with open addressing using linear probing, as described in CLRS (Introduction to Algorithms) Chapter 11.

## Implementation

**File**: `CLRS.Ch11.HashTable.fst`

### Hash Table Design

- **Data structure**: Fixed-size array of integers (`A.array int`)
- **Sentinel values**:
  - `-1` = empty slot
  - `-2` = deleted slot  
  - `>= 0` = valid stored key
- **Hash function**: `h(k) = k % table_size`
- **Collision resolution**: Linear probing with `h(k, i) = (h(k) + i) % table_size`

### Operations

1. **`hash_insert`**: Insert a non-negative key into the hash table
   - Returns `true` if insertion succeeds, `false` if table is full
   - Uses linear probing to find the first empty or deleted slot
   - Writes unconditionally (Pulse pattern for conditional writes)

2. **`hash_search`**: Search for a key in the hash table
   - Returns the index if found, or `size` (invalid index) if not found
   - Stops when key is found or an empty slot is encountered
   - Does not modify the table (preserves original array)

### Verification Properties

✅ **No admits or assumes** - All proofs are complete  
✅ **Memory safety** - All array accesses are within bounds  
✅ **Resource safety** - Proper separation logic with `pts_to` predicates  
✅ **Functional correctness** - Operations implement CLRS linear probing algorithm

### Preconditions

- `key >= 0` - Keys must be non-negative (to distinguish from sentinels)
- `SZ.fits key` - Keys must fit in a `size_t` type
- `size > 0` - Table must have positive size
- `Seq.length s == size` - Array length matches declared size

### Postconditions

- **`hash_insert`**: Returns table with potentially modified contents, preserving length
- **`hash_search`**: Returns table unchanged (same ghost sequence), result ≤ size

## Key Pulse Patterns Used

1. **Explicit array operations**: `A.op_Array_Access` and `A.op_Array_Assignment` instead of shorthand
2. **While loop syntax**: Condition uses `let` bindings: `while (let x = !r; condition)`
3. **Unconditional writes**: Compute new value with `if-then-else`, then write unconditionally
4. **Reference reads before conditionals**: Read `!r` before using in pure conditional expressions
5. **Parenthesized if-then-else**: Use `(if cond then x else y)` in let bindings
6. **Separation logic invariants**: `invariant exists* witnesses. slprop ** pure (...)`

## Building and Verification

```bash
# Verify the implementation
make verify

# Or verify manually
cd ch11-hash-tables
make -C .. verify
```

## Test File

**File**: `CLRS.Ch11.HashTable.Test.fst`

Demonstrates:
- Creating a hash table
- Inserting multiple keys with hash collisions
- Searching for present and absent keys
- Proper resource management (alloc/free)

## References

- CLRS 3rd Edition, Chapter 11: Hash Tables
- Section 11.4: Open Addressing
- Linear Probing: Simplest open addressing method
