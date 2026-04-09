module AVCHelper

module Seq = FStar.Seq

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
