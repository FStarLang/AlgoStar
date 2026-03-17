module CLRS.Ch16.Huffman.Defs
open FStar.SizeT
open FStar.Mul
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
module HSpec = CLRS.Ch16.Huffman.Spec
module HOpt = CLRS.Ch16.Huffman.Optimality
module PQ = Pulse.Lib.PriorityQueue
module Box = Pulse.Lib.Box
open Pulse.Lib.TotalOrder
open FStar.Order

#push-options "--z3rlimit 8"

// ========== PQ entry type: (frequency, index into nodes Vec) ==========

let pq_entry : eqtype = int & SZ.t

let valid_pq_entries (s: Seq.seq pq_entry) (n: nat) : prop =
  forall (j: nat). j < Seq.length s ==> SZ.v (snd (Seq.index s j)) < n

// All PQ entries have positive frequencies
let pq_freqs_positive (pq: Seq.seq pq_entry) : prop =
  forall (j: nat). j < Seq.length pq ==> fst (Seq.index pq j) > 0

// PQ index uniqueness: no two entries share the same snd (index) component
[@@ "opaque_to_smt"]
let pq_idx_unique (s: Seq.seq pq_entry) : prop =
  forall (i j: nat). i < Seq.length s /\ j < Seq.length s /\ i <> j ==>
    snd (Seq.index s i) <> snd (Seq.index s j)

// ========== Count helpers ==========

// If no element of s equals x, count x s = 0
let rec count_zero (#a: eqtype) (x: a) (s: Seq.seq a)
  : Lemma (requires forall (k: nat). k < Seq.length s ==> Seq.index s k <> x)
          (ensures FStar.Seq.Properties.count x s = 0)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      assert (Seq.head s == Seq.index s 0);
      let tl = Seq.tail s in
      let aux (k: nat{k < Seq.length tl}) : Lemma (Seq.index tl k <> x) =
        assert (Seq.index tl k == Seq.index s (k + 1))
      in
      Classical.forall_intro aux;
      count_zero x tl
    end

// If count x s = 1, then i and j both indexing x implies i = j
let rec count_one_unique (#a: eqtype) (x: a) (s: Seq.seq a) (i j: nat)
  : Lemma (requires FStar.Seq.Properties.count x s = 1 /\
                    i < Seq.length s /\ j < Seq.length s /\
                    Seq.index s i = x /\ Seq.index s j = x)
          (ensures i = j)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else if Seq.head s = x then begin
      // count x (tail s) = 0
      assert (FStar.Seq.Properties.count x (Seq.tail s) = 0);
      // So i = 0 and j = 0
      if i > 0 then begin
        assert (Seq.index (Seq.tail s) (i - 1) == Seq.index s i);
        FStar.Seq.Properties.mem_index x (Seq.tail s)
      end;
      if j > 0 then begin
        assert (Seq.index (Seq.tail s) (j - 1) == Seq.index s j);
        FStar.Seq.Properties.mem_index x (Seq.tail s)
      end
    end
    else begin
      // head <> x, so count x (tail s) = 1
      assert (FStar.Seq.Properties.count x (Seq.tail s) = 1);
      // i > 0 and j > 0
      assert (i > 0);
      assert (j > 0);
      assert (Seq.index (Seq.tail s) (i - 1) == Seq.index s i);
      assert (Seq.index (Seq.tail s) (j - 1) == Seq.index s j);
      count_one_unique x (Seq.tail s) (i - 1) (j - 1)
    end

// pq_idx_unique implies all entries are pairwise distinct, so count <= 1 for any element
let rec pq_idx_unique_count_le_1 (s: Seq.seq pq_entry) (x: pq_entry)
  : Lemma (requires pq_idx_unique s)
          (ensures FStar.Seq.Properties.count x s <= 1)
          (decreases Seq.length s)
  = reveal_opaque (`%pq_idx_unique) pq_idx_unique;
    if Seq.length s = 0 then ()
    else begin
      let hd = Seq.head s in
      let tl = Seq.tail s in
      if hd = x then begin
        // count x s = 1 + count x tl; show count x tl = 0
        let aux2 (k: nat{k < Seq.length tl}) : Lemma (Seq.index tl k <> x) =
          assert (Seq.index tl k == Seq.index s (k + 1));
          assert (snd (Seq.index s (k + 1)) <> snd (Seq.index s 0))
        in
        Classical.forall_intro aux2;
        count_zero x tl
      end
      else begin
        // hd <> x, count x s = count x tl; need pq_idx_unique tl
        assert (forall (i: nat) (j: nat). i < Seq.length tl /\ j < Seq.length tl /\ i <> j ==>
          Seq.index tl i == Seq.index s (i + 1) /\ Seq.index tl j == Seq.index s (j + 1));
        pq_idx_unique_count_le_1 tl x
      end
    end

// ========== PQ entry comparison ==========

let pq_entry_compare (x y: pq_entry) : order =
  let (fx, ix) = x in
  let (fy, iy) = y in
  if fx < fy then Lt
  else if fx > fy then Gt
  else if SZ.v ix < SZ.v iy then Lt
  else if SZ.v ix > SZ.v iy then Gt
  else Eq

instance pq_entry_total_order : total_order pq_entry = {
  compare = pq_entry_compare;
  properties = ()
}

// ========== List helper functions ==========

// Remove element at position j from a list
let rec list_remove_at (#a: Type) (l: list a) (j: nat{j < L.length l}) : list a =
  match l with
  | h :: t -> if j = 0 then t else h :: list_remove_at t (j - 1)

let rec list_remove_at_length (#a: Type) (l: list a) (j: nat{j < L.length l})
  : Lemma (ensures L.length (list_remove_at l j) == L.length l - 1) (decreases j)
  = match l with
    | _ :: t -> if j > 0 then list_remove_at_length t (j - 1)

// Index into list_remove_at: elements before j stay, elements after j shift down
let rec list_remove_at_index (#a: Type) (l: list a) (j: nat{j < L.length l}) (k: nat)
  : Lemma (requires k < L.length l - 1)
          (ensures L.length (list_remove_at l j) == L.length l - 1 /\
                   L.index (list_remove_at l j) k == (if k < j then L.index l k else L.index l (k + 1)))
          (decreases l)
  = list_remove_at_length l j;
    match l with
    | h :: t ->
      if j = 0 then ()
      else if k = 0 then ()
      else begin list_remove_at_length t (j - 1); list_remove_at_index t (j - 1) (k - 1) end

// Remove two elements from a list (remove j1 first, then adjust j2)
let list_remove_two (#a: Type) (l: list a) (j1 j2: nat)
  : Pure (list a) (requires j1 < L.length l /\ j2 < L.length l /\ j1 <> j2)
         (ensures fun _ -> True)
  = list_remove_at_length l j1;
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    list_remove_at (list_remove_at l j1) j2'

let list_remove_two_length (#a: Type) (l: list a) (j1 j2: nat)
  : Lemma (requires j1 < L.length l /\ j2 < L.length l /\ j1 <> j2)
          (ensures L.length (list_remove_two l j1 j2) == L.length l - 2)
  = list_remove_at_length l j1;
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    list_remove_at_length (list_remove_at l j1) j2'

// Removing element at position j changes count of that element by -1
let rec list_remove_at_count (#a: eqtype) (l: list a) (j: nat{j < L.length l}) (y: a)
  : Lemma (ensures L.count y (list_remove_at l j) == 
                   (if L.index l j = y then L.count y l - 1 else L.count y l))
          (decreases j)
  = match l with
    | h :: t ->
      if j = 0 then ()
      else list_remove_at_count t (j - 1) y

// All counts after removal
let list_remove_at_count_all (#a: eqtype) (l: list a) (j: nat{j < L.length l})
  : Lemma (ensures (forall (y: a). L.count y (list_remove_at l j) ==
                     (if L.index l j = y then L.count y l - 1 else L.count y l)))
  = Classical.forall_intro (Classical.move_requires (list_remove_at_count l j))

// Helper: for lists, if count of one element goes up by 1 and all others stay,
// then length goes up by 1
// Two lists with identical counts have the same length
let rec list_perm_length (#a: eqtype) (l0 l1: list a)
  : Lemma (requires forall (y:a). L.count y l0 == L.count y l1)
          (ensures L.length l0 == L.length l1)
          (decreases l0)
  = match l0 with
    | [] ->
      (match l1 with
       | [] -> ()
       | h :: _ -> assert (L.count h l1 >= 1); assert (L.count h l0 == 0))
    | h :: tl ->
      assert (L.count h l1 >= 1);
      LP.mem_count l1 h;
      let k = LP.index_of l1 h in
      let l1' = list_remove_at l1 k in
      list_remove_at_count l1 k h;
      list_remove_at_count_all l1 k;
      list_remove_at_length l1 k;
      list_perm_length tl l1'

// If count of one element goes up by 1 and all others stay, length goes up by 1
let rec list_count_length_step (#a: eqtype) (l0 l1: list a) (x: a)
  : Lemma (requires L.count x l1 == L.count x l0 + 1 /\
                    (forall (y:a). y =!= x ==> L.count y l1 == L.count y l0))
          (ensures L.length l1 == L.length l0 + 1)
          (decreases l1)
  = match l1 with
    | [] -> ()
    | h :: tl ->
      if h = x then begin
        // count x (h::tl) = 1 + count x tl, so count x tl = count x l0
        // For y <> x: count y tl = count y l0 (since h = x <> y)
        // So tl and l0 are permutations
        list_perm_length tl l0
      end else begin
        // h <> x: count h l0 >= 1 (since count h l1 = count h l0 and count h l1 >= 1)
        assert (L.count h l0 >= 1);
        LP.mem_count l0 h;
        let k = LP.index_of l0 h in
        let l0' = list_remove_at l0 k in
        list_remove_at_count l0 k x;
        list_remove_at_count_all l0 k;
        list_remove_at_length l0 k;
        // count x l0' = count x l0, count h l0' = count h l0 - 1
        // count x tl = count x l0 + 1 = count x l0' + 1
        // for y <> x, y <> h: count y tl = count y l0 = count y l0'
        // for y = h: count h tl = count h l1 - 1 = count h l0 - 1 = count h l0'
        list_count_length_step l0' tl x
        // length tl = length l0' + 1 = (length l0 - 1) + 1 = length l0
        // length l1 = 1 + length tl = length l0 + 1
      end

// ========== extends_length ==========

let extends_length (#t: eqtype) (s0 s1: Seq.seq t) (x: t)
  : Lemma (requires PQ.extends s0 s1 x)
          (ensures Seq.length s1 == Seq.length s0 + 1)
  = FStar.Seq.Properties.lemma_seq_to_list_permutation s0;
    FStar.Seq.Properties.lemma_seq_to_list_permutation s1;
    let l0 = Seq.seq_to_list s0 in
    let l1 = Seq.seq_to_list s1 in
    FStar.Seq.Properties.lemma_seq_list_bij s0;
    FStar.Seq.Properties.lemma_seq_list_bij s1;
    list_count_length_step l0 l1 x

// ========== Heap node types (needed by forest_entry) ==========

noeq type hnode = {
    sym: int;
    freq: int;
    left: option (Box.box hnode);
    right: option (Box.box hnode);
}
let hnode_ptr = Box.box hnode

// ========== Forest entry type ==========

let forest_entry = SZ.t & hnode_ptr & HSpec.htree
let entry_idx  (e: forest_entry) : SZ.t = let (i, _, _) = e in i
let entry_ptr  (e: forest_entry) : hnode_ptr = let (_, p, _) = e in p
let entry_tree (e: forest_entry) : HSpec.htree = let (_, _, t) = e in t

// Forest distinct indices: no two entries share the same index
[@@ "opaque_to_smt"]
let forest_distinct_indices (entries: list forest_entry) : prop =
  forall (i j: nat). i < L.length entries /\ j < L.length entries /\ i <> j ==>
    entry_idx (L.index entries i) <> entry_idx (L.index entries j)

let forest_distinct_indices_elim (entries: list forest_entry) (i j: nat)
  : Lemma (requires forest_distinct_indices entries /\ i < L.length entries /\ j < L.length entries /\ i <> j)
          (ensures entry_idx (L.index entries i) <> entry_idx (L.index entries j))
  = reveal_opaque (`%forest_distinct_indices) forest_distinct_indices

// ========== Find-entry helpers ==========

// Find position of a forest_entry by its SZ.t index
let rec find_entry_by_idx (entries: list forest_entry) (idx: SZ.t)
  : Tot (option nat) (decreases entries)
  = match entries with
    | [] -> None
    | hd :: tl -> if entry_idx hd = idx then Some 0
                  else (match find_entry_by_idx tl idx with
                        | None -> None
                        | Some k -> Some (k + 1))

let rec find_entry_by_idx_spec (entries: list forest_entry) (idx: SZ.t)
  : Lemma (ensures (match find_entry_by_idx entries idx with
                    | None -> forall (k: nat). k < L.length entries ==> entry_idx (L.index entries k) =!= idx
                    | Some k -> k < L.length entries /\ entry_idx (L.index entries k) == idx))
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd :: tl ->
      if entry_idx hd = idx then ()
      else begin
        find_entry_by_idx_spec tl idx;
        match find_entry_by_idx tl idx with
        | None -> ()
        | Some k -> ()
      end

// Distinct indices in a forest map to distinct positions via find_entry_by_idx
let find_entry_positions_distinct (entries: list forest_entry) (idx1 idx2: SZ.t)
  : Lemma (requires
      Some? (find_entry_by_idx entries idx1) /\
      Some? (find_entry_by_idx entries idx2) /\
      idx1 <> idx2)
    (ensures Some?.v (find_entry_by_idx entries idx1) <> Some?.v (find_entry_by_idx entries idx2))
  = find_entry_by_idx_spec entries idx1;
    find_entry_by_idx_spec entries idx2

// ========== PQ-forest predicates ==========

// Every PQ entry index appears in the forest
let pq_indices_in_forest (pq: Seq.seq pq_entry) (forest: list forest_entry) : prop =
  forall (j: nat). j < Seq.length pq ==>
    Some? (find_entry_by_idx forest (snd (Seq.index pq j)))

// ========== seq_to_pos_list ==========

// Convert a sequence of positive ints to a list of pos, starting from index k
// Elements <= 0 are clamped to 1 (shouldn't happen with valid input)
let rec seq_to_pos_list (s: Seq.seq int) (k: nat)
  : Tot (list pos) (decreases Seq.length s - k)
  = if k >= Seq.length s then []
    else
      let v : pos = if Seq.index s k > 0 then Seq.index s k else 1 in
      v :: seq_to_pos_list s (k + 1)

let rec seq_to_pos_list_length (s: Seq.seq int) (k: nat)
  : Lemma (ensures L.length (seq_to_pos_list s k) == (if k >= Seq.length s then 0 else Seq.length s - k))
          (decreases Seq.length s - k)
  = if k >= Seq.length s then ()
    else seq_to_pos_list_length s (k + 1)

// ========== all_leaf_freqs ==========

// All leaf frequencies across the forest
let rec all_leaf_freqs (entries: list forest_entry) : list pos =
  match entries with
  | [] -> []
  | e :: rest -> L.append (HSpec.leaf_freqs (entry_tree e)) (all_leaf_freqs rest)

// count distributes over all_leaf_freqs cons
let all_leaf_freqs_cons (e: forest_entry) (rest: list forest_entry) (x: pos)
  : Lemma (L.count x (all_leaf_freqs (e :: rest)) ==
           L.count x (HSpec.leaf_freqs (entry_tree e)) + L.count x (all_leaf_freqs rest))
  = LP.append_count (HSpec.leaf_freqs (entry_tree e)) (all_leaf_freqs rest) x

// Splitting all_leaf_freqs at position j
let rec all_leaf_freqs_remove_at (entries: list forest_entry) (j: nat) (x: pos)
  : Lemma (requires j < L.length entries)
          (ensures L.count x (all_leaf_freqs entries) ==
                   L.count x (HSpec.leaf_freqs (entry_tree (L.index entries j))) +
                   L.count x (all_leaf_freqs (list_remove_at entries j)))
          (decreases j)
  = match entries with
    | e :: rest ->
      all_leaf_freqs_cons e rest x;
      if j = 0 then ()
      else begin
        list_remove_at_length entries j;
        all_leaf_freqs_remove_at rest (j - 1) x;
        all_leaf_freqs_cons e (list_remove_at rest (j - 1)) x
      end

// ========== Leaf label validity ==========

// Per-tree property: every leaf has a valid sym mapping to the input array
let tree_leaf_labels_valid (ft: HSpec.htree) (freq_seq: Seq.seq int) : prop =
  forall (sf: (nat & pos)). L.mem sf (HSpec.leaf_labels ft) ==>
    fst sf < Seq.length freq_seq /\ Seq.index freq_seq (fst sf) == snd sf

// Forest-level: all trees satisfy leaf label validity (recursive definition)
let rec forest_leaf_labels_valid (active: list forest_entry) (freq_seq: Seq.seq int) : prop =
  match active with
  | [] -> True
  | e :: rest -> tree_leaf_labels_valid (entry_tree e) freq_seq /\
                 forest_leaf_labels_valid rest freq_seq

// Index-based accessor for forest_leaf_labels_valid
let rec forest_leaf_labels_valid_index
  (active: list forest_entry) (j: nat) (freq_seq: Seq.seq int)
  : Lemma (requires forest_leaf_labels_valid active freq_seq /\ j < L.length active)
          (ensures tree_leaf_labels_valid (entry_tree (L.index active j)) freq_seq)
          (decreases j)
  = match active with
    | _ :: rest -> if j = 0 then () else forest_leaf_labels_valid_index rest (j - 1) freq_seq

// Merging two trees preserves leaf label validity
let tree_leaf_labels_valid_internal (l r: HSpec.htree) (f: pos) (freq_seq: Seq.seq int)
  : Lemma (requires tree_leaf_labels_valid l freq_seq /\ tree_leaf_labels_valid r freq_seq)
          (ensures tree_leaf_labels_valid (HSpec.Internal f l r) freq_seq)
  = LP.append_mem_forall (HSpec.leaf_labels l) (HSpec.leaf_labels r)

// Adding a valid tree to the front preserves forest validity
let forest_leaf_labels_valid_cons
  (idx: SZ.t) (p: hnode_ptr) (ft: HSpec.htree) (active: list forest_entry) (freq_seq: Seq.seq int)
  : Lemma (requires tree_leaf_labels_valid ft freq_seq /\
                    forest_leaf_labels_valid active freq_seq)
          (ensures forest_leaf_labels_valid ((idx, p, ft) :: active) freq_seq)
  = ()

// Removing one element preserves forest validity
let rec forest_leaf_labels_valid_remove_at
  (active: list forest_entry) (j: nat) (freq_seq: Seq.seq int)
  : Lemma (requires forest_leaf_labels_valid active freq_seq /\ j < L.length active)
          (ensures forest_leaf_labels_valid (list_remove_at active j) freq_seq)
          (decreases j)
  = match active with
    | _ :: rest ->
      if j = 0 then ()
      else forest_leaf_labels_valid_remove_at rest (j - 1) freq_seq

// Removing two elements preserves forest validity
let forest_leaf_labels_valid_remove_two
  (active: list forest_entry) (j1 j2: nat) (freq_seq: Seq.seq int)
  : Lemma (requires forest_leaf_labels_valid active freq_seq /\
                    j1 < L.length active /\ j2 < L.length active /\ j1 <> j2)
          (ensures forest_leaf_labels_valid (list_remove_two active j1 j2) freq_seq)
  = forest_leaf_labels_valid_remove_at active j1 freq_seq;
    list_remove_at_length active j1;
    let j2' : nat = if j2 < j1 then j2 else j2 - 1 in
    forest_leaf_labels_valid_remove_at (list_remove_at active j1) j2' freq_seq

// ========== Cost tracking infrastructure ==========

// Sum of HSpec.cost of all trees in the active forest
let rec forest_total_cost (entries: list forest_entry) : nat =
  match entries with
  | [] -> 0
  | e :: rest -> HSpec.cost (entry_tree e) + forest_total_cost rest

// List of root frequencies of all trees in the active forest
let rec forest_root_freqs (entries: list forest_entry) : list pos =
  match entries with
  | [] -> []
  | e :: rest -> HSpec.freq_of (entry_tree e) :: forest_root_freqs rest

// ========== PQ search ==========

// Search PQ for an entry with a given index
let rec find_pq_idx (pq: Seq.seq pq_entry) (target_idx: SZ.t) (i: nat)
  : Tot (option nat) (decreases Seq.length pq - i)
  = if i >= Seq.length pq then None
    else if snd (Seq.index pq i) = target_idx then Some i
    else find_pq_idx pq target_idx (i + 1)

let rec find_pq_idx_spec (pq: Seq.seq pq_entry) (target_idx: SZ.t) (i: nat)
  : Lemma (ensures (match find_pq_idx pq target_idx i with
                    | None -> forall (j: nat). i <= j /\ j < Seq.length pq ==> snd (Seq.index pq j) <> target_idx
                    | Some j -> i <= j /\ j < Seq.length pq /\ snd (Seq.index pq j) == target_idx))
          (decreases Seq.length pq - i)
  = if i >= Seq.length pq then ()
    else if snd (Seq.index pq i) = target_idx then ()
    else find_pq_idx_spec pq target_idx (i + 1)

// ========== Opaque predicate definitions ==========

// PQ entry freq matches the tree root freq at the found position
[@@ "opaque_to_smt"]
let pq_entry_freq_ok (f: int) (idx: SZ.t) (active: list forest_entry) : prop =
  match find_entry_by_idx active idx with
  | Some k -> if k < L.length active then f == HSpec.freq_of (entry_tree (L.index active k)) else False
  | None -> False

// PQ entry frequencies match forest tree root frequencies
[@@ "opaque_to_smt"]
let pq_tree_freq_match (pq: Seq.seq pq_entry) (active: list forest_entry) : prop =
  forall (j: nat). j < Seq.length pq ==>
    pq_entry_freq_ok (fst (Seq.index pq j)) (snd (Seq.index pq j)) active

// Opaque wrapper: no PQ entry has snd == idx
[@@ "opaque_to_smt"]
let pq_no_idx (pq: Seq.seq pq_entry) (idx: SZ.t) : prop =
  forall (j: nat). j < Seq.length pq ==> snd (Seq.index pq j) <> idx

// Every forest entry has a corresponding PQ entry
[@@ "opaque_to_smt"]
let forest_has_pq_entry (pq: Seq.seq pq_entry) (active: list forest_entry) : prop =
  forall (k: nat). k < L.length active ==>
    Some? (find_pq_idx pq (entry_idx (L.index active k)) 0)

// ========== forest_all_leaves ==========

[@@ "opaque_to_smt"]
let forest_all_leaves (active: list forest_entry) : prop =
  forall (k: nat). k < L.length active ==> HSpec.Leaf? (entry_tree (L.index active k))

// ========== Opaque bundle predicates ==========

[@@ "opaque_to_smt"]
let init_bundle (freq_seq: Seq.seq int) (nd_contents: Seq.seq hnode_ptr)
                (pq: Seq.seq pq_entry) (active: list forest_entry) (vi: nat) (n: nat) : prop =
  Seq.length nd_contents == n /\
  vi <= n /\
  valid_pq_entries pq n /\
  pq_freqs_positive pq /\
  pq_idx_unique pq /\
  forest_distinct_indices active /\
  pq_indices_in_forest pq active /\
  pq_tree_freq_match pq active /\
  forest_has_pq_entry pq active /\
  forest_total_cost active == 0 /\
  (forall (k: nat). k < L.length active ==>
    SZ.v (entry_idx (L.index active k)) < vi /\
    SZ.v (entry_idx (L.index active k)) < n /\
    Seq.index nd_contents (SZ.v (entry_idx (L.index active k))) == entry_ptr (L.index active k)) /\
  (forall (x: pos). L.count x (all_leaf_freqs active) + L.count x (seq_to_pos_list freq_seq vi) ==
                     L.count x (seq_to_pos_list freq_seq 0))

[@@ "opaque_to_smt"]
let merge_bundle (freq_seq: Seq.seq int) (nd_contents: Seq.seq hnode_ptr)
                 (pq: Seq.seq pq_entry) (active: list forest_entry) (n: nat) : prop =
  SZ.fits n /\
  Seq.length nd_contents == n /\
  valid_pq_entries pq n /\
  pq_freqs_positive pq /\
  pq_idx_unique pq /\
  pq_indices_in_forest pq active /\
  pq_tree_freq_match pq active /\
  forest_has_pq_entry pq active /\
  forest_distinct_indices active /\
  (forall (k: nat). k < L.length active ==>
    SZ.v (entry_idx (L.index active k)) < n /\
    Seq.index nd_contents (SZ.v (entry_idx (L.index active k))) == entry_ptr (L.index active k)) /\
  (forall (x: pos). L.count x (all_leaf_freqs active) == L.count x (seq_to_pos_list freq_seq 0)) /\
  forest_total_cost active + HOpt.greedy_cost (forest_root_freqs active) ==
    HOpt.greedy_cost (seq_to_pos_list freq_seq 0)

#pop-options
