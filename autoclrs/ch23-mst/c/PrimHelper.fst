module PrimHelper

open FStar.Mul

module SZ = FStar.SizeT

/// Pure function to compute base = u * n for flat matrix indexing.
/// Uses NLArith.base_bound to establish nonlinear arithmetic facts
/// that Z3 cannot prove on its own.
let compute_base (u n weights_len: SZ.t)
  : Pure SZ.t
    (requires SZ.v u < SZ.v n /\ 0 < SZ.v n /\ SZ.v weights_len == SZ.v n * SZ.v n)
    (ensures fun base -> SZ.v base == SZ.v u * SZ.v n /\ SZ.v base + SZ.v n <= SZ.v weights_len)
  = NLArith.base_bound (SZ.v u) (SZ.v n);
    SZ.mul u n
