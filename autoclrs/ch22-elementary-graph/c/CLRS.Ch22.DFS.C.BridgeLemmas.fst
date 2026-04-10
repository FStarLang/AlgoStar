(**
 * Bridge lemmas for DFS C-to-Pulse verification.
 *
 * Uses SizeT.t quantifiers throughout to match c2pulse's generated code.
 * This avoids the nat<->SizeT bridging issue that defeats Z3 trigger matching.
 *)
module CLRS.Ch22.DFS.C.BridgeLemmas

open FStar.Mul
module Seq = FStar.Seq
module I32 = FStar.Int32
module SZ  = FStar.SizeT

(* The finish ordering predicate using SZ.t quantifiers.
   Matches c2pulse's _forall(size_t v, ...) format exactly. *)
let pred_finish_ok_c
  (scolor sf: Seq.seq (option I32.t))
  (spred: Seq.seq (option SZ.t))
  (sz_n: SZ.t)
  : prop
  = let n = SZ.v sz_n in
    Seq.length scolor >= n /\ Seq.length sf >= n /\ Seq.length spred >= n /\
    (forall (i:SZ.t). SZ.v i < n ==> Some? (Seq.index scolor (SZ.v i))) /\
    (forall (i:SZ.t). SZ.v i < n ==> Some? (Seq.index sf (SZ.v i))) /\
    (forall (i:SZ.t). SZ.v i < n ==> Some? (Seq.index spred (SZ.v i))) /\
    (forall (v:SZ.t). SZ.v v < n /\
      I32.v (Some?.v (Seq.index scolor (SZ.v v))) == 2 /\
      SZ.v (Some?.v (Seq.index spred (SZ.v v))) < n /\
      I32.v (Some?.v (Seq.index scolor (SZ.v (Some?.v (Seq.index spred (SZ.v v)))))) == 2
    ==>
      I32.v (Some?.v (Seq.index sf (SZ.v v))) <
      I32.v (Some?.v (Seq.index sf (SZ.v (Some?.v (Seq.index spred (SZ.v v)))))))

(** Finish ordering is preserved when finishing vertex u.
    Takes OLD (pre-write) arrays; proves the property for POST-write arrays.
    Called BEFORE writing f[u] := new_time and color[u] := 2.
    All quantifiers use SZ.t to match c2pulse-generated hypotheses. *)
#push-options "--z3rlimit 160 --fuel 1 --ifuel 1 --split_queries always"
let finish_ordering_preserved
  (old_color old_f: Seq.seq (option I32.t))
  (spred: Seq.seq (option SZ.t))
  (sz_n sz_u: SZ.t) (new_time: I32.t)
  : Lemma
    (requires
      (let n = SZ.v sz_n in let u = SZ.v sz_u in
       pred_finish_ok_c old_color old_f spred sz_n /\
       u < n /\ n > 0 /\
       Some? (Seq.index old_color u) /\
       I32.v (Some?.v (Seq.index old_color u)) == 1 /\
       (* All BLACK vertices have f < new_time *)
       (forall (j:SZ.t). SZ.v j < n /\
         Some? (Seq.index old_color (SZ.v j)) /\
         I32.v (Some?.v (Seq.index old_color (SZ.v j))) == 2 ==>
         Some? (Seq.index old_f (SZ.v j)) /\
         I32.v (Some?.v (Seq.index old_f (SZ.v j))) < I32.v new_time) /\
       (* Parent of u is not BLACK or u has no valid parent *)
       Some? (Seq.index spred u) /\
       (SZ.v (Some?.v (Seq.index spred u)) >= n \/
        (SZ.v (Some?.v (Seq.index spred u)) < n /\
         Some? (Seq.index old_color (SZ.v (Some?.v (Seq.index spred u)))) /\
         I32.v (Some?.v (Seq.index old_color (SZ.v (Some?.v (Seq.index spred u))))) <> 2)) /\
       (* u is not its own parent *)
       (SZ.v (Some?.v (Seq.index spred u)) >= n \/
        SZ.v (Some?.v (Seq.index spred u)) <> u)))
    (ensures
       pred_finish_ok_c
        (Seq.upd old_color (SZ.v sz_u) (Some 2l))
        (Seq.upd old_f (SZ.v sz_u) (Some new_time))
        spred sz_n)
  = ()
#pop-options

(** Vacuously true: if no vertex is BLACK, pred_finish_ok_c holds trivially.
    Used at the Phase 1 to Phase 2 transition in dfs. *)
let pred_finish_ok_c_init
  (scolor sf: Seq.seq (option I32.t))
  (spred: Seq.seq (option SZ.t))
  (sz_n: SZ.t)
  : Lemma
    (requires
      (let n = SZ.v sz_n in
       Seq.length scolor >= n /\ Seq.length sf >= n /\ Seq.length spred >= n /\
       (forall (i:SZ.t). SZ.v i < n ==> Some? (Seq.index scolor (SZ.v i))) /\
       (forall (i:SZ.t). SZ.v i < n ==> Some? (Seq.index sf (SZ.v i))) /\
       (forall (i:SZ.t). SZ.v i < n ==> Some? (Seq.index spred (SZ.v i))) /\
       (forall (v:SZ.t). SZ.v v < n ==>
         I32.v (Some?.v (Seq.index scolor (SZ.v v))) <> 2)))
    (ensures pred_finish_ok_c scolor sf spred sz_n)
  = ()
