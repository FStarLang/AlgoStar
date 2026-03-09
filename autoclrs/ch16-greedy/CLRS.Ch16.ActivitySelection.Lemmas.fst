module CLRS.Ch16.ActivitySelection.Lemmas

open FStar.Seq

(* Lemma: extending the selection with a new compatible activity *)
let lemma_extend_selection
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
    // earliest_compatible for sel':
    // 1. Between consecutive old elements (i+1 < |sel|): sel'[i] = sel[i], same as old
    // 2. Between sel[last] and new_idx: old "after last" covers sel[last] < z < processed = new_idx
    // 3. After new_idx: vacuously true (new_idx < z < new_idx+1 is empty)
    assert (earliest_compatible sel' s f n (new_idx + 1));
    ()

(* Lemma: when we skip an activity (not selected), the invariant is preserved *)
let lemma_skip_activity
  (sel: seq nat) (s f: seq int) (n: nat) (processed: nat) (last_finish: int)
  : Lemma
    (requires greedy_selection_inv sel s f n processed last_finish /\ processed < n /\
             processed < Seq.length s /\ processed < Seq.length f /\
             // The skipped activity is incompatible (start < last_finish)
             Seq.index s processed < last_finish)
    (ensures greedy_selection_inv sel s f n (processed + 1) last_finish)
  = // earliest_compatible: "after last" part extends from processed to processed+1
    // processed has start < last_finish = finish[sel[last]], so it's incompatible
    ()

(* Combined step lemma: handles both select and skip cases *)
let lemma_step
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

(* ====== OPTIMALITY PROOF ====== *)

//SNIPPET_START: lemma_greedy_choice_seq
(* Greedy choice property (CLRS Theorem 16.1):
   Given any valid selection, we can replace its first element with 0
   (the earliest-finishing activity) and get another valid selection.
   
   This proves: there exists an optimal solution containing activity 0.
   
   Proof sketch:
   - Let k = sel[0] be the first selected activity
   - Since activities are sorted by finish time: f[0] <= f[k]
   - If sel has > 1 element, let j = sel[1]
   - From pairwise compatibility: f[k] <= s[j]
   - By transitivity: f[0] <= f[k] <= s[j]
   - So replacing k with 0 preserves compatibility
   - strictly_increasing is preserved since 0 <= k < j
*)
let lemma_greedy_choice (s f: seq int) (n: nat) (opt: seq nat)
  : Lemma 
    (requires 
      is_valid_selection opt s f n /\
      finish_sorted f /\
      n == Seq.length s /\ n == Seq.length f /\ n > 0 /\
      (forall (i:nat). i < n ==> valid_activity s f i))
    (ensures
      (let opt' = Seq.upd opt 0 0 in
       is_valid_selection opt' s f n /\ Seq.length opt' == Seq.length opt))
//SNIPPET_END: lemma_greedy_choice_seq
  = let k = Seq.index opt 0 in
    let opt' = Seq.upd opt 0 0 in
    
    // Length is preserved by upd
    assert (Seq.length opt' == Seq.length opt);
    
    // Key fact: f[0] <= f[k] (from finish_sorted)
    assert (k < n);  // from all_valid_indices
    assert (Seq.index f 0 <= Seq.index f k);
    
    // Prove all_valid_indices for opt'
    // opt'[i] = if i = 0 then 0 else opt[i]
    // 0 < n by hypothesis, and for i > 0, opt'[i] = opt[i] < n
    let aux_valid (i: nat{i < Seq.length opt'})
      : Lemma (ensures Seq.index opt' i < n)
      = if i = 0 then 
          assert (Seq.index opt' 0 == 0)
        else 
          assert (Seq.index opt' i == Seq.index opt i)
    in
    FStar.Classical.forall_intro aux_valid;
    assert (all_valid_indices opt' n);
    
    // Prove strictly_increasing for opt'
    // Need: for all i < j, opt'[i] < opt'[j]
    // Case 1: i = 0, j > 0: need 0 < opt'[j] = opt[j]
    //   Since opt is strictly_increasing: opt[0] < opt[j]
    //   Since opt[0] = k >= 0: we have opt[j] > k >= 0, so opt[j] > 0 unless k = 0
    //   If k = 0, then opt' = opt, so done
    // Case 2: i > 0, j > i: opt'[i] = opt[i] < opt[j] = opt'[j] ✓
    let aux_strict (i: nat{i < Seq.length opt'}) (j: nat{i < j /\ j < Seq.length opt'})
      : Lemma (ensures Seq.index opt' i < Seq.index opt' j)
      = if i = 0 then begin
          // opt'[0] = 0, opt'[j] = opt[j]
          // Need: 0 < opt[j]
          // From strictly_increasing: opt[0] < opt[j]
          // opt[0] = k >= 0, so if k = 0, then opt[j] > 0
          // If k > 0, then opt[j] > k > 0
          assert (Seq.index opt 0 < Seq.index opt j);
          assert (Seq.index opt 0 == k);
          assert (Seq.index opt j > k);
          assert (k >= 0);
          if k = 0 then 
            assert (Seq.index opt' j > 0)
          else begin
            assert (k > 0);
            assert (Seq.index opt j > k);
            assert (Seq.index opt j > 0)
          end;
          assert (Seq.index opt' 0 == 0);
          assert (Seq.index opt' j == Seq.index opt j);
          assert (Seq.index opt' 0 < Seq.index opt' j)
        end
        else begin
          assert (Seq.index opt' i == Seq.index opt i);
          assert (Seq.index opt' j == Seq.index opt j);
          assert (Seq.index opt i < Seq.index opt j)
        end
    in
    // Introduce the nested quantifiers manually
    let aux_strict_j (i: nat{i < Seq.length opt'}) (j: nat{j < Seq.length opt'})
      : Lemma (requires i < j)
              (ensures Seq.index opt' i < Seq.index opt' j)
      = aux_strict i j
    in
    let aux_strict_i (i: nat{i < Seq.length opt'})
      : Lemma (ensures forall (j: nat). i < j /\ j < Seq.length opt' ==> Seq.index opt' i < Seq.index opt' j)
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (aux_strict_j i))
    in
    FStar.Classical.forall_intro aux_strict_i;
    assert (strictly_increasing opt');
    
    // Prove pairwise_compatible for opt'
    // First part: all indices are valid (already proved above)
    let aux_compat_idx (i: nat{i < Seq.length opt'})
      : Lemma (ensures Seq.index opt' i < Seq.length s /\ Seq.index opt' i < Seq.length f)
      = if i = 0 then begin
          assert (Seq.index opt' 0 == 0);
          assert (0 < n);
          assert (n == Seq.length s);
          assert (n == Seq.length f)
        end
        else begin
          assert (Seq.index opt' i == Seq.index opt i)
        end
    in
    FStar.Classical.forall_intro aux_compat_idx;
    
    // Second part: consecutive pairs are compatible
    let aux_compat_pairs (i: nat{i + 1 < Seq.length opt'})
      : Lemma (ensures Seq.index f (Seq.index opt' i) <= Seq.index s (Seq.index opt' (i + 1)))
      = if i = 0 then begin
          // Need: f[opt'[0]] <= s[opt'[1]]
          // opt'[0] = 0, opt'[1] = opt[1]
          // From pairwise_compatible opt: f[opt[0]] <= s[opt[1]]
          // opt[0] = k
          // So: f[k] <= s[opt[1]]
          // From finish_sorted: f[0] <= f[k]
          // By transitivity: f[0] <= s[opt[1]]
          assert (Seq.index opt' 0 == 0);
          assert (Seq.index opt' 1 == Seq.index opt 1);
          assert (Seq.index f (Seq.index opt 0) <= Seq.index s (Seq.index opt 1));
          assert (Seq.index f k <= Seq.index s (Seq.index opt 1));
          assert (Seq.index f 0 <= Seq.index f k);
          assert (Seq.index f 0 <= Seq.index s (Seq.index opt 1));
          assert (Seq.index f (Seq.index opt' 0) <= Seq.index s (Seq.index opt' 1))
        end
        else begin
          assert (Seq.index opt' i == Seq.index opt i);
          assert (Seq.index opt' (i + 1) == Seq.index opt (i + 1));
          assert (Seq.index f (Seq.index opt i) <= Seq.index s (Seq.index opt (i + 1)))
        end
    in
    FStar.Classical.forall_intro aux_compat_pairs;
    assert (pairwise_compatible opt' s f);
    
    // All components of is_valid_selection are proved
    assert (is_valid_selection opt' s f n)
