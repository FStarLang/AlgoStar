module AVCHelper

open FStar.Mul
open FStar.List.Tot
module Seq = FStar.Seq
module Spec = CLRS.Ch35.VertexCover.Spec

(* Total helper: read integer value from a sequence at index i, defaulting to 0 *)
let seq_val (s: Seq.seq (option Int32.t)) (i: nat) : int =
  if i < Seq.length s
  then match Seq.index s i with
       | Some x -> Int32.v x
       | None -> 0
  else 0

(* Cover validity for all scanned rows < u:
   for every edge (u2,v2) with u2 < u, u2 < v2 < n,
   either adj[u2*n+v2] = 0 or cover[u2] != 0 or cover[v2] != 0 *)
let covers_upto
  (sa sc: Seq.seq (option Int32.t)) (n u: nat) : prop =
  forall (u2 v2: nat).
    (u2 < u /\ u2 < v2 /\ v2 < n) ==>
    (seq_val sa (u2 `op_Multiply` n + v2) = 0 \/
     seq_val sc u2 <> 0 \/
     seq_val sc v2 <> 0)

(* Cover validity for current row u, columns u+1..v-1 *)
let covers_row
  (sa sc: Seq.seq (option Int32.t)) (n u v: nat) : prop =
  forall (v2: nat).
    (u < v2 /\ v2 < v) ==>
    (seq_val sa (u `op_Multiply` n + v2) = 0 \/
     seq_val sc u <> 0 \/
     seq_val sc v2 <> 0)

(* Binary property: all cover values are 0 or 1 *)
let binary (sc: Seq.seq (option Int32.t)) (n: nat) : prop =
  forall (i: nat). i < n ==>
    (seq_val sc i = 0 \/ seq_val sc i = 1)

(* Combined outer loop invariant: covers all rows < u and cover is binary *)
let outer_inv_pure (sa sc: Seq.seq (option Int32.t)) (n u: nat) : prop =
  Seq.length sa = n `op_Multiply` n /\
  Seq.length sc = n /\
  covers_upto sa sc n u /\
  binary sc n

(* Combined inner loop invariant: also covers current row up to column v *)
let inner_inv_pure (sa sc: Seq.seq (option Int32.t)) (n u v: nat) : prop =
  Seq.length sa = n `op_Multiply` n /\
  Seq.length sc = n /\
  covers_upto sa sc n u /\
  covers_row sa sc n u v /\
  binary sc n

(* ── Matching invariant for c2pulse (option Int32.t sequences) ─────── *)

(* The matching tracks edges selected by the greedy algorithm.
   Vertices in the cover correspond exactly to matching endpoints. *)
let matching_inv_opt (sa sc: Seq.seq (option Int32.t)) (n: nat) (m: list Spec.edge) : prop =
  Seq.length sa = n `op_Multiply` n /\
  Seq.length sc = n /\
  Spec.pairwise_disjoint m /\
  (forall (e: Spec.edge). memP e m ==>
    (let (u, v) = e in u < n /\ v < n /\ u <> v /\ u < v /\
      seq_val sa (u `op_Multiply` n + v) <> 0)) /\
  (forall (x: nat). x < n ==>
    ((seq_val sc x <> 0) == existsb (fun (e: Spec.edge) -> Spec.edge_uses_vertex e x) m))

(* Helper: existsb returning false means f is false for all elements *)
let rec existsb_false_means_all_false_opt (#a: Type) (f: a -> bool) (l: list a)
  : Lemma (requires existsb f l == false)
          (ensures forall (x: a). memP x l ==> f x == false)
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> existsb_false_means_all_false_opt f tl

(* Step lemma: matching_inv_opt is maintained when adding a new edge *)
#push-options "--z3rlimit 80"
let matching_inv_add_opt
  (sa sc: Seq.seq (option Int32.t)) (n vu vv: nat) (m: list Spec.edge)
  : Lemma
    (requires
      matching_inv_opt sa sc n m /\
      vu < n /\ vv < n /\ vu < vv /\
      seq_val sa (vu `op_Multiply` n + vv) <> 0 /\
      seq_val sc vu = 0 /\ seq_val sc vv = 0)
    (ensures (
      let sc1 = Seq.upd sc vu (Some (Int32.int_to_t 1)) in
      let sc2 = Seq.upd sc1 vv (Some (Int32.int_to_t 1)) in
      matching_inv_opt sa sc2 n ((vu, vv) :: m)))
  = existsb_false_means_all_false_opt (fun (e: Spec.edge) -> Spec.edge_uses_vertex e vu) m;
    existsb_false_means_all_false_opt (fun (e: Spec.edge) -> Spec.edge_uses_vertex e vv) m
#pop-options

(* Variant taking Seq.index values directly — matches Pulse's rewrites_to postconditions *)
#push-options "--z3rlimit 80"
let matching_inv_add_opt_idx
  (sa sc: Seq.seq (option Int32.t)) (n vu vv: nat) (m: list Spec.edge)
  (he cu cv: Int32.t)
  : Lemma
    (requires
      matching_inv_opt sa sc n m /\
      vu < n /\ vv < n /\ vu < vv /\
      Seq.index sa (vu `op_Multiply` n + vv) == Some he /\ he <> Int32.int_to_t 0 /\
      Seq.index sc vu == Some cu /\ cu == Int32.int_to_t 0 /\
      Seq.index sc vv == Some cv /\ cv == Int32.int_to_t 0)
    (ensures (
      let sc1 = Seq.upd sc vu (Some (Int32.int_to_t 1)) in
      let sc2 = Seq.upd sc1 vv (Some (Int32.int_to_t 1)) in
      matching_inv_opt sa sc2 n ((vu, vv) :: m)))
  = matching_inv_add_opt sa sc n vu vv m
#pop-options

(* Unconditional step lemma: handles both add-edge and no-op cases.
   Mirrors the Pulse reference implementation's matching_inv_step. *)
#push-options "--z3rlimit 80"
let matching_inv_step_opt
  (sa sc: Seq.seq (option Int32.t)) (n vu vv: nat) (m: list Spec.edge)
  (he cu cv new_cu new_cv: Int32.t)
  : Lemma
    (requires
      matching_inv_opt sa sc n m /\
      vu < n /\ vv < n /\ vu < vv /\
      Seq.index sa (vu `op_Multiply` n + vv) == Some he /\
      Seq.index sc vu == Some cu /\
      Seq.index sc vv == Some cv /\
      new_cu == (if Int32.v he <> 0 && Int32.v cu = 0 && Int32.v cv = 0
                 then Int32.int_to_t 1 else cu) /\
      new_cv == (if Int32.v he <> 0 && Int32.v cu = 0 && Int32.v cv = 0
                 then Int32.int_to_t 1 else cv))
    (ensures (
      let s1 = Seq.upd sc vu (Some new_cu) in
      let s2 = Seq.upd s1 vv (Some new_cv) in
      let new_m = if Int32.v he <> 0 && Int32.v cu = 0 && Int32.v cv = 0
                  then (vu, vv) :: m else m in
      matching_inv_opt sa s2 n new_m))
  = if Int32.v he <> 0 && Int32.v cu = 0 && Int32.v cv = 0 then
      matching_inv_add_opt sa sc n vu vv m
    else ()
#pop-options
