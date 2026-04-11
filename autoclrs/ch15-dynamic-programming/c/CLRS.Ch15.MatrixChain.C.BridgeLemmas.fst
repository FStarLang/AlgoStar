module CLRS.Ch15.MatrixChain.C.BridgeLemmas

open FStar.Seq
module I32 = FStar.Int32

open CLRS.Ch15.MatrixChain.Spec
open FStar.Mul

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

let mc_result_from_table (dims: seq int) (n: nat) (table: seq int)
  : Lemma (requires n > 0 /\ length dims = n + 1 /\ length table = n * n /\
                    table == mc_outer (create (n * n) 0) dims n 2)
          (ensures index table (n - 1) == mc_result dims n)
  = lemma_mc_outer_len (create (n * n) 0) dims n 2

(* When l > n, mc_outer is the identity *)
let mc_outer_identity (table: seq int) (dims: seq int) (n l: nat)
  : Lemma (requires l > n)
          (ensures mc_outer table dims n l == table)
  = ()

(* mc_outer step: unfold one level when l <= n *)
let mc_outer_unfold (table: seq int) (dims: seq int) (n l: nat)
  : Lemma (requires l <= n)
          (ensures mc_outer table dims n l == mc_outer (mc_inner_i table dims n l 0) dims n (l + 1))
  = ()

(* mc_inner_i base case: identity when i + l > n *)
let mc_inner_i_base (table: seq int) (dims: seq int) (n l i: nat)
  : Lemma (requires i + l > n \/ l < 2)
          (ensures mc_inner_i table dims n l i == table)
  = ()

(* Bridge: if to_int_seq of an option-seq equals create nn 0, we can use it as init *)
let to_int_seq_create_zero (s: seq (option I32.t)) (nn: nat)
  : Lemma (requires Seq.length s = nn /\
                    (forall (i: nat). i < nn ==> Seq.index (to_int_seq s) i == 0))
          (ensures to_int_seq s == Seq.create nn 0)
  = assert (Seq.equal (to_int_seq s) (Seq.create nn 0))

(* Bridge: after writing table[idx] = min_cost where min_cost = mc_inner_k(...),
   mc_inner_i at i+1 on the updated table equals mc_inner_i at i on the old table.
   
   Works at seq int level (post to_int_seq conversion) so the SMTPat fires
   AFTER to_int_seq_upd_some has rewritten to_int_seq(Seq.upd ...) → Seq.upd(to_int_seq ...). *)
let mc_inner_i_write_step (table: seq int) (dims: seq int)
  (n l i: nat) (min_cost: int) (idx: nat)
  : Lemma
      (requires
        Seq.length table = n * n /\
        Seq.length dims = n + 1 /\
        n >= 1 /\ l >= 2 /\ l <= n /\ i + l <= n /\
        idx = i * n + (i + l - 1) /\
        idx < Seq.length table /\
        min_cost == mc_inner_k table dims n i (i+l-1) i 1000000000)
      (ensures
        mc_inner_i (Seq.upd table idx min_cost) dims n l (i + 1)
        == mc_inner_i table dims n l i)
      [SMTPat (mc_inner_i (Seq.upd table idx min_cost) dims n l (i + 1))]
  = ()

(* Combined bridge: works at seq (option I32.t) level — fires directly on 
   the term c2pulse generates after array_write, avoiding the two-step 
   SMTPat chain (to_int_seq_upd_some → mc_inner_i_write_step). *)
let mc_inner_i_write_opt (s: seq (option I32.t)) (dims_s: seq (option I32.t))
  (n l i: nat) (min_cost: I32.t) (idx: nat)
  : Lemma
      (requires
        Seq.length s = n * n /\
        Seq.length dims_s = n + 1 /\
        n >= 1 /\ l >= 2 /\ l <= n /\ i + l <= n /\
        idx = i * n + (i + l - 1) /\
        idx < Seq.length s /\
        I32.v min_cost == mc_inner_k (to_int_seq s) (to_int_seq dims_s) n i (i+l-1) i 1000000000)
      (ensures
        mc_inner_i (to_int_seq (Seq.upd s idx (Some min_cost))) (to_int_seq dims_s) n l (i + 1)
        == mc_inner_i (to_int_seq s) (to_int_seq dims_s) n l i)
      [SMTPat (mc_inner_i (to_int_seq (Seq.upd s idx (Some min_cost))) (to_int_seq dims_s) n l (i + 1))]
  = to_int_seq_upd_some s idx min_cost

(* Full i-loop step: takes old mc_outer invariant, produces new mc_outer invariant
   on the post-write state. Called explicitly so the conclusion is directly available
   at the i-loop invariant check — no multi-step Z3 reasoning needed. *)
(* Base case: when k >= j, mc_inner_k returns min_acc unchanged *)
let mc_inner_k_base (table: seq int) (dims: seq int) (n i j k: nat) (min_acc: int)
  : Lemma (requires k >= j)
          (ensures mc_inner_k table dims n i j k min_acc == min_acc)
  = ()

(* Explicit one-step unfolding of mc_inner_k.
   Called inside the k-loop body so Z3 doesn't need fuel to unfold. *)
let mc_inner_k_step (table: seq int) (dims: seq int) (n i j k: nat) (min_acc: int)
  : Lemma
      (requires k < j /\ i < n /\ j < n /\ length table = n * n /\ length dims = n + 1)
      (ensures (
        let cost_ik = index table (i * n + k) in
        let cost_k1j = index table ((k + 1) * n + j) in
        let dim_i = index dims i in
        let dim_k1 = index dims (k + 1) in
        let dim_j1 = index dims (j + 1) in
        let q = cost_ik + cost_k1j + dim_i * dim_k1 * dim_j1 in
        let new_min = if q < min_acc then q else min_acc in
        mc_inner_k table dims n i j (k + 1) new_min ==
        mc_inner_k table dims n i j k min_acc))
  = ()

let mc_i_step_full (s: seq (option I32.t)) (dims_s: seq (option I32.t))
  (n l i: nat) (min_cost: I32.t) (idx: nat)
  : Lemma
      (requires
        Seq.length s = n * n /\
        Seq.length dims_s = n + 1 /\
        n >= 1 /\ l >= 2 /\ l <= n /\ i + l <= n /\
        idx = i * n + (i + l - 1) /\
        idx < Seq.length s /\
        I32.v min_cost == mc_inner_k (to_int_seq s) (to_int_seq dims_s) n i (i+l-1) i 1000000000 /\
        mc_outer (mc_inner_i (to_int_seq s) (to_int_seq dims_s) n l i)
                 (to_int_seq dims_s) n (l + 1)
          == mc_outer (Seq.create (n * n) 0) (to_int_seq dims_s) n 2)
      (ensures
        mc_outer (mc_inner_i (to_int_seq (Seq.upd s idx (Some min_cost))) (to_int_seq dims_s) n l (i + 1))
                 (to_int_seq dims_s) n (l + 1)
          == mc_outer (Seq.create (n * n) 0) (to_int_seq dims_s) n 2)
  = to_int_seq_upd_some s idx min_cost
