module CLRS.Ch16.ActivitySelection.Lemmas

open FStar.Seq

(* Activities are sorted by finish time *)
let finish_sorted (f: seq int) : prop =
  forall (i j: nat). i <= j /\ j < Seq.length f ==> Seq.index f i <= Seq.index f j

(* Valid activity: start <= finish *)
let valid_activity (s f: seq int) (i: nat) : prop =
  i < Seq.length s /\ i < Seq.length f /\ Seq.index s i <= Seq.index f i

(* Selected activities: a sequence of indices into the activity arrays *)

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

(* The full greedy selection invariant *)
let greedy_selection_inv (sel: seq nat) (s f: seq int) (n: nat) (processed: nat) (last_finish: int) : prop =
  // Basic properties
  Seq.length sel >= 1 /\
  all_valid_indices sel n /\
  strictly_increasing sel /\
  pairwise_compatible sel s f /\
  // All selected indices are in [0, processed)
  (forall (i: nat). i < Seq.length sel ==> Seq.index sel i < processed) /\
  // last_finish is the finish time of the last selected activity
  Seq.index sel (Seq.length sel - 1) < Seq.length f /\
  Seq.index f (Seq.index sel (Seq.length sel - 1)) == last_finish /\
  // First selected is index 0
  Seq.index sel 0 == 0

(* Lemma: extending the selection with a new compatible activity *)
let lemma_extend_selection
  (sel: seq nat) (s f: seq int) (n: nat) (processed: nat) (last_finish: int) (new_idx: nat)
  : Lemma
    (requires
      greedy_selection_inv sel s f n processed last_finish /\
      new_idx < n /\
      new_idx >= processed /\ new_idx < Seq.length s /\ new_idx < Seq.length f /\
      Seq.index s new_idx >= last_finish /\
      n == Seq.length s /\ n == Seq.length f)
    (ensures
      (let sel' = Seq.snoc sel new_idx in
       greedy_selection_inv sel' s f n (new_idx + 1) (Seq.index f new_idx)))
  = let suffix = Seq.create 1 new_idx in
    let sel' = Seq.append sel suffix in
    // Length
    Seq.Base.lemma_len_append sel suffix;
    assert (Seq.length sel' == Seq.length sel + 1);
    // Indexing: for i < length sel, sel'[i] == sel[i]
    let aux_idx (i: nat{i < Seq.length sel})
      : Lemma (ensures i < Seq.length sel' /\ Seq.index sel' i == Seq.index sel i)
      = Seq.Base.lemma_index_app1 sel suffix i
    in
    FStar.Classical.forall_intro aux_idx;
    // sel'[length sel] == new_idx
    Seq.Base.lemma_index_app2 sel suffix (Seq.length sel);
    assert (Seq.index sel' (Seq.length sel) == Seq.index suffix 0);
    assert (Seq.index suffix 0 == new_idx);
    assert (Seq.index sel' (Seq.length sel) == new_idx);
    // all_valid_indices
    assert (all_valid_indices sel' n);
    // strictly_increasing: need new_idx > all previous selections
    // Since all previous selections < processed and new_idx >= processed
    assert (forall (i:nat). i < Seq.length sel ==> Seq.index sel' i < processed);
    assert (new_idx >= processed);
    assert (strictly_increasing sel');
    // pairwise_compatible for new pair
    assert (Seq.index f (Seq.index sel (Seq.length sel - 1)) == last_finish);
    assert (Seq.index s new_idx >= last_finish);
    assert (pairwise_compatible sel' s f);
    // last element
    assert (Seq.index sel' (Seq.length sel' - 1) == new_idx);
    ()

(* Lemma: when we skip an activity (not selected), the invariant is preserved *)
let lemma_skip_activity
  (sel: seq nat) (s f: seq int) (n: nat) (processed: nat) (last_finish: int)
  : Lemma
    (requires greedy_selection_inv sel s f n processed last_finish /\ processed < n)
    (ensures greedy_selection_inv sel s f n (processed + 1) last_finish)
  = ()

(* Combined step lemma: handles both select and skip cases *)
let lemma_step
  (sel: seq nat) (s f: seq int) (n: nat) (processed: nat) (last_finish: int) (selected: bool)
  : Lemma
    (requires 
      greedy_selection_inv sel s f n processed last_finish /\
      processed < n /\ processed < Seq.length s /\ processed < Seq.length f /\
      n == Seq.length s /\ n == Seq.length f /\
      (selected ==> Seq.index s processed >= last_finish))
    (ensures
      (if selected then
        greedy_selection_inv (Seq.snoc sel processed) s f n (processed + 1) (Seq.index f processed) /\
        Seq.length (Seq.snoc sel processed) == Seq.length sel + 1
       else
        greedy_selection_inv sel s f n (processed + 1) last_finish /\
        Seq.length sel == Seq.length sel))
  = if selected then begin
      lemma_extend_selection sel s f n processed last_finish processed;
      let sel' = Seq.snoc sel processed in
      Seq.Base.lemma_len_append sel (Seq.create 1 processed);
      ()
    end
    else lemma_skip_activity sel s f n processed last_finish

(* Lemma: initial selection of activity 0 *)
let lemma_initial_selection (s f: seq int) (n: nat)
  : Lemma
    (requires n > 0 /\ n == Seq.length s /\ n == Seq.length f)
    (ensures 
      (let sel = Seq.create 1 0 in
       greedy_selection_inv sel s f n 1 (Seq.index f 0)))
  = let sel = Seq.create 1 0 in
    assert (Seq.length sel == 1);
    assert (Seq.index sel 0 == 0);
    ()
