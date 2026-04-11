module CLRS.Ch15.LCS.C.BridgeLemmas

open FStar.Seq
module I32 = FStar.Int32

open CLRS.Ch15.LCS.Spec

let to_int_seq (s: seq (option I32.t)) : seq int =
  Seq.init (Seq.length s) (fun i ->
    match Seq.index s i with
    | Some x -> I32.v x
    | None -> 0)

let to_int_seq_length (s: seq (option I32.t))
  : Lemma (ensures Seq.length (to_int_seq s) = Seq.length s)
          [SMTPat (Seq.length (to_int_seq s))]
  = ()

let to_int_seq_index (s: seq (option I32.t)) (i: nat)
  : Lemma (requires i < Seq.length s /\ Some? (Seq.index s i))
          (ensures Seq.index (to_int_seq s) i == I32.v (Some?.v (Seq.index s i)))
          [SMTPat (Seq.index (to_int_seq s) i)]
  = ()

let to_int_seq_upd_some (s: seq (option I32.t)) (j: nat) (v: I32.t)
  : Lemma (requires j < Seq.length s)
          (ensures to_int_seq (Seq.upd s j (Some v)) == Seq.upd (to_int_seq s) j (I32.v v))
          [SMTPat (to_int_seq (Seq.upd s j (Some v)))]
  = assert (Seq.equal (to_int_seq (Seq.upd s j (Some v))) (Seq.upd (to_int_seq s) j (I32.v v)))

open FStar.Mul

(* Unconditional bridge for lcs_table_correct diagonal bound.
   When i >= 1 /\ j >= 1, the diag value is at most i-1 (hence <= 999).
   Called BEFORE the if block to avoid ghost-inside-branch issues. *)
let lcs_table_diag_bound_opt (x y: seq int) (tbl: seq int) (m n i j: nat)
  : Lemma
      (requires
        lcs_table_correct x y tbl m n i j /\
        m == Seq.length x /\ n == Seq.length y /\
        i <= m /\ j <= n /\
        Seq.length tbl == (m + 1) * (n + 1))
      (ensures
        i >= 1 /\ j >= 1 ==>
          Seq.index tbl ((i - 1) * (n + 1) + (j - 1)) <= i - 1)
  = if i >= 1 && j >= 1 then
      lcs_length_upper_bound x y (i - 1) (j - 1)
    else ()

(* Bridge: final table result equals lcs_length *)
let lcs_table_result (x y: seq int) (tbl: seq int) (m n: nat)
  : Lemma
      (requires
        lcs_table_correct x y tbl m n (m + 1) 0 /\
        m == Seq.length x /\ n == Seq.length y)
      (ensures
        Seq.index tbl (m * (n + 1) + n) == lcs_length x y m n)
  = ()
