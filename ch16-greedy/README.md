# Activity Selection - Greedy Algorithm (Verified in Pulse)

## Overview
This implementation provides a verified greedy algorithm for the Activity Selection problem from CLRS Chapter 16.

## Algorithm
Given a set of activities with start and finish times (sorted by finish time), the algorithm selects the maximum number of non-overlapping activities.

**Greedy Strategy**: Always select the activity that finishes earliest among the remaining compatible activities.

## Implementation Details

### Input
- `start_times`: Array of activity start times
- `finish_times`: Array of activity finish times (pre-sorted by finish time)
- `n`: Number of activities (must be > 0)

### Output
- `count`: Number of selected activities (SZ.t)

### Preconditions
1. Both arrays have length n
2. Activities are sorted by finish time
3. Each activity is valid (start ≤ finish)

### Postconditions
1. At least one activity is selected: `count ≥ 1`
2. At most n activities selected: `count ≤ n`

## Verification
The implementation is fully verified in Pulse with:
- **NO admits**
- **NO assumes**
- Complete loop invariants
- Proper separation logic for array access

## Building
```bash
cd /home/nswamy/workspace/clrs/ch16-greedy
rm -rf .depend _cache
make _cache/CLRS.Ch16.ActivitySelection.fst.checked
```

## Key Specifications

### finish_sorted
```fstar
let finish_sorted (f: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\ j < Seq.length f ==> 
    Seq.index f i <= Seq.index f j
```

### compatible
```fstar
let compatible (s f: Seq.seq int) (i j: nat) : prop =
  i < Seq.length s /\ j < Seq.length s /\
  i < Seq.length f /\ j < Seq.length f /\
  Seq.index f i <= Seq.index s j
```

### valid_activity
```fstar
let valid_activity (s f: Seq.seq int) (i: nat) : prop =
  i < Seq.length s /\ i < Seq.length f /\ 
  Seq.index s i <= Seq.index f i
```

## Loop Invariant
The algorithm maintains:
1. `vi` tracks current position (1 ≤ vi ≤ n)
2. `vcount` tracks selected activities (1 ≤ vcount ≤ vi)
3. `vlast_finish` is the finish time of the last selected activity
4. `vlast_finish` is a valid finish time from activities [0, vi)

## Time Complexity
O(n) - single linear scan through the activities

## Notes
- This is a read-only algorithm (arrays are accessed with permission `#p`)
- The algorithm assumes activities are pre-sorted by finish time
- Full optimality proof (showing this equals the maximum independent set) would require additional theorems, but the basic correctness properties are proven
