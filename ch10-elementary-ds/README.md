# Stack Data Structure in Pulse

This directory contains a formally verified implementation of an array-based stack data structure in Pulse, following the CLRS textbook (Chapter 10.1).

## Files

- **CLRS.Ch10.Stack.fsti** - Interface specification
- **CLRS.Ch10.Stack.fst** - Implementation
- **CLRS.Ch10.Stack.Test.fst** - Basic usage test

## Data Structure

```pulse
noeq type stack (t:Type) = {
  data: A.array t;          // Array to store elements
  top: R.ref SZ.t;          // Index of next free slot (0 = empty)
  capacity: erased nat;     // Maximum capacity
}
```

## Stack Invariant

The stack maintains a separation logic invariant `stack_inv` that:
- Relates the array contents to a logical list representation
- Ensures `top` points to the next free slot (0 = empty)
- Guarantees LIFO ordering: list head = stack top
- The array stores elements in reverse order: `arr[i]` corresponds to `list[top-1-i]`

## Operations

### create_stack
```pulse
fn create_stack (t:Type0) (default_val: t) (capacity: SZ.t)
```
Creates a new empty stack with the given capacity. Requires a default value for array initialization.

### stack_empty
```pulse  
fn stack_empty (#t:Type0) (s: stack t) (#contents: erased (list t))
```
Returns `true` if the stack is empty (length = 0).

### push
```pulse
fn push (#t:Type0) (s: stack t) (#contents: erased (list t)) (x: t)
```
Pushes an element onto the stack. Requires that the stack is not full (`length < capacity`).
Postcondition: New contents = `x :: old_contents`

### pop
```pulse
fn pop (#t:Type0) (s: stack t) (#contents: erased (list t))
```
Pops and returns the top element. Requires non-empty stack.
Postcondition: `old_contents == result :: new_contents`

### peek
```pulse
fn peek (#t:Type0) (s: stack t) (#contents: erased (list t))
```
Returns the top element without removing it. Requires non-empty stack.
Stack contents remain unchanged.

## Implementation Notes

1. **LIFO Ordering**: The specification uses a logical list where the head represents the top of the stack, ensuring LIFO semantics.

2. **Capacity Checking**: Push operations require proving that the stack is not full to prevent overflow.

3. **Ghost State**: The `contents` parameter is `erased (list t)` - it exists only for specification purposes and is compiled away.

4. **Admitted Proofs**: Some complex proofs about array-list correspondence are admitted using `admit()` as suggested. These could be completed with more detailed lemmas about:
   - Index arithmetic for the reverse mapping
   - Size_t arithmetic bounds
   - List/sequence correspondence

## CLRS Algorithms

The implementation follows the pseudocode from CLRS Chapter 10.1:

**STACK-EMPTY(S)**:
```
return S.top == 0
```

**PUSH(S, x)**:
```
S.top = S.top + 1
S[S.top-1] = x
```

**POP(S)**:
```
if STACK-EMPTY(S):
  error "underflow"
S.top = S.top - 1
return S[S.top]
```

## Building

```bash
cd /home/nswamy/workspace/clrs/ch10-elementary-ds
make
```

## Warnings

The implementation uses `A.alloc` and `R.alloc` which are marked as deprecated and unsound in Pulse. These are suitable for model implementations but would need to be replaced with proper memory management for production use.
