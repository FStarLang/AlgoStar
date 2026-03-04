(*
   Activity Selection — Lemmas Interface

   Predicate definitions and lemma signatures for the greedy
   activity selection invariant (CLRS §16.1).
*)
module CLRS.Ch16.ActivitySelection.Lemmas

open FStar.Seq

(* Activities are sorted by finish time *)
let finish_sorted (f: seq int) : prop =
  forall (i j: nat). i <= j /\ j < Seq.length f ==> Seq.index f i <= Seq.index f j

(* Valid activity: start < finish (CLRS assumes strict inequality) *)
let valid_activity (s f: seq int) (i: nat) : prop =
  i < Seq.length s /\ i < Seq.length f /\ Seq.index s i < Seq.index f i

(* All indices are valid *)
let all_valid_indices (sel: seq nat) (n: nat) : prop =
  forall (i: nat). i < Seq.length sel ==> Seq.index sel i < n

(* Indices are strictly increasing *)
let strictly_increasing (sel: seq nat) : prop =
  forall (i j: nat). i < j /\ j < Seq.length sel ==> Seq.index sel i < Seq.index sel j

(* Selected activities are pairwise non-overlapping:
   for consecutive selected activities, finish[sel[i]] <= start[sel[i+1]] *)
let pairwise_compatible (sel: seq nat) (s f: seq int) : prop =
  (forall (i: nat). i < Seq.length sel ==> Seq.index sel i < Seq.length s /\ Seq.index sel i < Seq.length f) /\
  (forall (i: nat). i + 1 < Seq.length sel ==>
    Seq.index f (Seq.index sel i) <= Seq.index s (Seq.index sel (i + 1)))

(* Earliest-compatible property: each selected activity is the earliest compatible one. *)
let earliest_compatible (sel: seq nat) (s f: seq int) (n: nat) (processed: nat) : prop =
  Seq.length sel >= 1 /\
  (forall (i: nat). i + 1 < Seq.length sel ==>
    (forall (z: nat). Seq.index sel i < z /\ z < Seq.index sel (i + 1) /\
                       z < n /\ z < Seq.length s /\ z < Seq.length f ==>
      Seq.index s z < Seq.index f (Seq.index sel i))) /\
  (forall (z: nat). Seq.index sel (Seq.length sel - 1) < z /\ z < processed /\
                     z < n /\ z < Seq.length s /\ z < Seq.length f ==>
    Seq.index s z < Seq.index f (Seq.index sel (Seq.length sel - 1)))

(* The full greedy selection invariant *)
let greedy_selection_inv (sel: seq nat) (s f: seq int) (n: nat) (processed: nat) (last_finish: int) : prop =
  Seq.length sel >= 1 /\
  all_valid_indices sel n /\
  strictly_increasing sel /\
  pairwise_compatible sel s f /\
  (forall (i: nat). i < Seq.length sel ==> Seq.index sel i < processed) /\
  Seq.index sel (Seq.length sel - 1) < Seq.length f /\
  Seq.index f (Seq.index sel (Seq.length sel - 1)) == last_finish /\
  Seq.index sel 0 == 0 /\
  earliest_compatible sel s f n processed

(* A valid selection: a compatible set of activities *)
let is_valid_selection (sel: seq nat) (s f: seq int) (n: nat) : prop =
  Seq.length sel >= 1 /\
  all_valid_indices sel n /\
  strictly_increasing sel /\
  pairwise_compatible sel s f

(* Lemma: extending the selection with a new compatible activity *)
val lemma_extend_selection
  (sel: seq nat) (s f: seq int) (n: nat) (processed: nat) (last_finish: int) (new_idx: nat)
  : Lemma
    (requires
      greedy_selection_inv sel s f n processed last_finish /\
      new_idx < n /\
      new_idx == processed /\ new_idx < Seq.length s /\ new_idx < Seq.length f /\
      Seq.index s new_idx >= last_finish /\
      n == Seq.length s /\ n == Seq.length f)
    (ensures
      (let sel' = Seq.snoc sel new_idx in
       greedy_selection_inv sel' s f n (new_idx + 1) (Seq.index f new_idx)))

(* Lemma: when we skip an activity, the invariant is preserved *)
val lemma_skip_activity
  (sel: seq nat) (s f: seq int) (n: nat) (processed: nat) (last_finish: int)
  : Lemma
    (requires greedy_selection_inv sel s f n processed last_finish /\ processed < n /\
             processed < Seq.length s /\ processed < Seq.length f /\
             Seq.index s processed < last_finish)
    (ensures greedy_selection_inv sel s f n (processed + 1) last_finish)

(* Combined step lemma *)
val lemma_step
  (sel: seq nat) (s f: seq int) (n: nat) (processed: nat) (last_finish: int) (selected: bool)
  : Lemma
    (requires 
      greedy_selection_inv sel s f n processed last_finish /\
      processed < n /\ processed < Seq.length s /\ processed < Seq.length f /\
      n == Seq.length s /\ n == Seq.length f /\
      (selected ==> Seq.index s processed >= last_finish) /\
      (not selected ==> Seq.index s processed < last_finish))
    (ensures
      (if selected then
        greedy_selection_inv (Seq.snoc sel processed) s f n (processed + 1) (Seq.index f processed) /\
        Seq.length (Seq.snoc sel processed) == Seq.length sel + 1
       else
        greedy_selection_inv sel s f n (processed + 1) last_finish /\
        Seq.length sel == Seq.length sel))

(* Lemma: initial selection of activity 0 *)
val lemma_initial_selection (s f: seq int) (n: nat)
  : Lemma
    (requires n > 0 /\ n == Seq.length s /\ n == Seq.length f)
    (ensures 
      (let sel = Seq.create 1 0 in
       greedy_selection_inv sel s f n 1 (Seq.index f 0)))

(* Greedy choice property (CLRS Theorem 16.1) *)
val lemma_greedy_choice (s f: seq int) (n: nat) (opt: seq nat)
  : Lemma 
    (requires 
      is_valid_selection opt s f n /\
      finish_sorted f /\
      n == Seq.length s /\ n == Seq.length f /\ n > 0 /\
      (forall (i:nat). i < n ==> valid_activity s f i))
    (ensures
      (let opt' = Seq.upd opt 0 0 in
       is_valid_selection opt' s f n /\ Seq.length opt' == Seq.length opt))
