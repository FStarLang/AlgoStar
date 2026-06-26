module CLRS.Common.Complexity.DivideConquer.Class
open Pulse
#lang-pulse

module A = Pulse.Lib.Array
module MR = Pulse.Lib.MonotonicGhostRef
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TO = Pulse.Lib.TotalOrder
open FStar.Order

let preorder_nat : FStar.Preorder.preorder nat = fun (x y:nat) -> b2t (x <= y)

let ticks_t = MR.mref #nat preorder_nat

let instrumented_total_order (a:Type) (ord:TO.total_order a) (ctr:ticks_t) =
  fn (x y:a) (#i:erased nat)
  requires MR.pts_to ctr #1.0R i
  returns o:order
  ensures MR.pts_to ctr #1.0R (i + 1)
  ensures pure (o == x `ord.TO.compare` y)

let instrumented_binary_op (a:Type) (op:a -> a -> Tot a) (ctr:ticks_t) =
  fn (x y:a) (#i:erased nat)
  requires MR.pts_to ctr #1.0R i
  returns z:a
  ensures MR.pts_to ctr #1.0R (i + 1)
  ensures pure (z == op x y)

let rec log2_floor (n:nat) : Tot nat (decreases n) =
  if n <= 1 then 0 else 1 + log2_floor (n / 2)

let binary_search_bound (n:nat) : nat = log2_floor n + 1

let max_subarray_bound (n:nat) : nat = 3 * n

let matrix_multiply_bound (n:nat) : nat = 2 * n * n * n

let flat_index (n i j:nat) : nat = i * n + j

let sorted (#a:Type) (ord:erased (TO.total_order a)) (s:Seq.seq a) : prop =
  forall (i j:nat). {:pattern (Seq.index s i); (Seq.index s j)}
    i < j /\ j < Seq.length s ==> le (Seq.index s i `ord.TO.compare` Seq.index s j)

let binary_search_correct (#a:Type) (s:Seq.seq a) (key:a) (result:nat) : prop =
  result <= Seq.length s /\
  (result < Seq.length s ==> Seq.index s result == key) /\
  (result == Seq.length s ==> forall (i:nat). i < Seq.length s ==> Seq.index s i =!= key)

noeq
type ordered_monoid (a:Type0) = {
  om_ord: TO.total_order a;
  om_zero: a;
  om_add: a -> a -> Tot a;
}

let max_ord (#a:Type) (ops:ordered_monoid a) (x y:a) : Tot a =
  if gt (y `ops.om_ord.TO.compare` x) then y else x

let rec kadane_spec (#a:Type) (ops:ordered_monoid a) (s:Seq.seq a) (i:nat)
  (current_sum:a) (best_sum:a)
  : Pure a
      (requires i <= Seq.length s)
      (ensures fun _ -> True)
      (decreases (if i <= Seq.length s then Seq.length s - i else 0))
  =
  if i >= Seq.length s then best_sum
  else
    let elem = Seq.index s i in
    let new_current = max_ord ops elem (ops.om_add current_sum elem) in
    let new_best = max_ord ops best_sum new_current in
    kadane_spec ops s (i + 1) new_current new_best

let max_subarray_spec (#a:Type) (ops:ordered_monoid a) (s:Seq.seq a) : Tot a =
  if Seq.length s = 0 then ops.om_zero
  else kadane_spec ops s 0 ops.om_zero (Seq.index s 0)

noeq
type semiring (a:Type0) = {
  sr_zero: a;
  sr_add: a -> a -> Tot a;
  sr_mul: a -> a -> Tot a;
}

let rec dot_product_spec (#a:Type) (ops:semiring a) (sa sb:Seq.seq a)
  (n i j:nat) (limit:nat)
  : Tot a (decreases limit)
  =
  if limit = 0 || i >= n || j >= n || n = 0 then ops.sr_zero
  else if limit > n then dot_product_spec ops sa sb n i j n
  else
    let k = limit - 1 in
    if flat_index n i k >= Seq.length sa || flat_index n k j >= Seq.length sb then ops.sr_zero
    else
      ops.sr_add
        (dot_product_spec ops sa sb n i j (limit - 1))
        (ops.sr_mul
          (Seq.index sa (flat_index n i k))
          (Seq.index sb (flat_index n k j)))

let mat_mul_correct (#a:Type) (ops:semiring a) (sa sb sc:Seq.seq a) (n:nat) : prop =
  Seq.length sc == n * n /\
  (forall (i j:nat). {:pattern (Seq.index sc (flat_index n i j))}
    i < n /\ j < n ==> Seq.index sc (flat_index n i j) == dot_product_spec ops sa sb n i j n)

let mat_mul_partial_k (#a:Type) (ops:semiring a) (sa sb sc:Seq.seq a)
  (n i j k:nat) : prop =
  Seq.length sc == n * n /\ i < n /\ j < n /\ k <= n /\
  Seq.index sc (flat_index n i j) == dot_product_spec ops sa sb n i j k

let mat_mul_partial_ij (#a:Type) (ops:semiring a) (sa sb sc:Seq.seq a)
  (n ri cj:nat) : prop =
  Seq.length sc == n * n /\
  (forall (i j:nat). {:pattern (Seq.index sc (flat_index n i j))}
    (i < ri \/ (i == ri /\ j < cj)) /\ i < n /\ j < n ==>
    Seq.index sc (flat_index n i j) == dot_product_spec ops sa sb n i j n)

class array_binary_search (f:nat -> nat) = {
  search:
    (fn (a:Type0)
        (#p:perm)
        (arr:A.array a)
        (len:SZ.t)
        (key:a)
        (ctr:ticks_t)
        (#ord:erased (TO.total_order a))
        (iord:instrumented_total_order a ord ctr)
        (#s:erased (Seq.seq a))
        (#i:erased nat)
      preserves A.pts_to arr #p s
      requires MR.pts_to ctr #1.0R i **
        pure (SZ.v len == Seq.length s /\ Seq.length s <= A.length arr /\ sorted ord s)
      returns result:SZ.t
      ensures exists* ticks.
        MR.pts_to ctr #1.0R ticks **
        pure (binary_search_correct s key (SZ.v result) /\
              ticks <= i + f (Seq.length s)));
}

class array_max_subarray (f:nat -> nat) = {
  max_subarray:
    (fn (a:Type0)
        (#p:perm)
        (arr:A.array a)
        (len:SZ.t)
        (ctr:ticks_t)
        (#ops:erased (ordered_monoid a))
        (iadd:instrumented_binary_op a ops.om_add ctr)
        (icmp:instrumented_total_order a ops.om_ord ctr)
        (#s:erased (Seq.seq a))
        (#i:erased nat)
      preserves A.pts_to arr #p s
      requires MR.pts_to ctr #1.0R i **
        pure (SZ.v len == Seq.length s /\ Seq.length s <= A.length arr /\ SZ.v len > 0)
      returns result:a
      ensures exists* ticks.
        MR.pts_to ctr #1.0R ticks **
        pure (result == max_subarray_spec ops s /\ ticks <= i + f (Seq.length s)));
}

class square_matrix_multiply (f:nat -> nat) = {
  multiply:
    (fn (a:Type0)
        (#pa #pb:perm)
        (ma:A.array a)
        (mb:A.array a)
        (mc:A.array a)
        (n:SZ.t)
        (ctr:ticks_t)
        (#ops:erased (semiring a))
        (iadd:instrumented_binary_op a ops.sr_add ctr)
        (imul:instrumented_binary_op a ops.sr_mul ctr)
        (#sa:erased (Seq.seq a))
        (#sb:erased (Seq.seq a))
        (#sc:erased (Seq.seq a))
        (#i:erased nat)
      requires
        A.pts_to ma #pa sa **
        A.pts_to mb #pb sb **
        A.pts_to mc sc **
        MR.pts_to ctr #1.0R i **
        pure (
          SZ.v n > 0 /\
          SZ.fits (SZ.v n * SZ.v n) /\
          Seq.length sa == SZ.v n * SZ.v n /\
          Seq.length sb == SZ.v n * SZ.v n /\
          Seq.length sc == SZ.v n * SZ.v n)
      ensures exists* sc' ticks.
        A.pts_to ma #pa sa **
        A.pts_to mb #pb sb **
        A.pts_to mc sc' **
        MR.pts_to ctr #1.0R ticks **
        pure (mat_mul_correct ops sa sb sc' (SZ.v n) /\ ticks <= i + f (SZ.v n)));
}
