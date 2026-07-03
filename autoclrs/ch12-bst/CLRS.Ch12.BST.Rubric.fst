module CLRS.Ch12.BST.Rubric
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Order

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module MR = Pulse.Lib.MonotonicGhostRef
module SC = CLRS.Common.Complexity.Search.Class
module TO = Pulse.Lib.TotalOrder

type bst (a:Type0) =
  | Leaf : bst a
  | Node : left:bst a -> key:a -> right:bst a -> bst a

noeq
type bst_node (a:Type0) = {
  key: a;
  left: bst_ptr a;
  right: bst_ptr a;
  p: bst_ptr a;
}
and bst_node_ptr (a:Type) = box (bst_node a)
and bst_ptr (a:Type) = option (bst_node_ptr a)

let rec height (a:Type0) (t:bst a) : nat =
  match t with
  | Leaf -> 0
  | Node l _ r ->
      1 + (if height a l >= height a r then height a l else height a r)

let rec size (a:Type0) (t:bst a) : nat =
  match t with
  | Leaf -> 0
  | Node l _ r -> 1 + size a l + size a r

let empty_model (a:Type0) : GTot (bst a) = Leaf

let rec find_model (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : GTot (option a)
  =
  match t with
  | Leaf -> None
  | Node l k r ->
      let c = key `ord.TO.compare` k in
      if lt c then find_model a ord l key
      else if gt c then find_model a ord r key
      else Some k

let rec insert_model (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : GTot (bst a)
  =
  match t with
  | Leaf -> Node Leaf key Leaf
  | Node l k r ->
      let c = key `ord.TO.compare` k in
      if lt c then Node (insert_model a ord l key) k r
      else if gt c then Node l k (insert_model a ord r key)
      else t

let rec minimum_model (a:Type0) (t:bst a) : option a =
  match t with
  | Leaf -> None
  | Node Leaf k _ -> Some k
  | Node l _ _ -> minimum_model a l

let rec delete_model (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : GTot (bst a)
  =
  match t with
  | Leaf -> Leaf
  | Node l k r ->
      let c = key `ord.TO.compare` k in
      if lt c then
        Node (delete_model a ord l key) k r
      else if gt c then
        Node l k (delete_model a ord r key)
      else
        match l, r with
        | Leaf, Leaf -> Leaf
        | Leaf, _ -> r
        | _, Leaf -> l
        | _, _ ->
            match minimum_model a r with
            | Some successor -> Node l successor (delete_model a ord r successor)
            | None -> t

// ============================================================
// Genuine BST validity: all_lt/all_gt/is_bst (bool-valued)
// ============================================================

let lt_ord (a:Type0) (ord:erased (TO.total_order a)) (x y:a) : GTot bool =
  lt (ord.TO.compare x y)

let gt_ord (a:Type0) (ord:erased (TO.total_order a)) (x y:a) : GTot bool =
  gt (ord.TO.compare x y)

let rec all_lt (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (bound:a) : GTot bool =
  match t with
  | Leaf -> true
  | Node l v r -> lt_ord a ord v bound && all_lt a ord l bound && all_lt a ord r bound

let rec all_gt (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (bound:a) : GTot bool =
  match t with
  | Leaf -> true
  | Node l v r -> gt_ord a ord v bound && all_gt a ord l bound && all_gt a ord r bound

let rec is_bst (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) : GTot bool =
  match t with
  | Leaf -> true
  | Node l k r ->
      is_bst a ord l &&
      is_bst a ord r &&
      all_lt a ord l k &&
      all_gt a ord r k

let valid (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) : GTot prop =
  is_bst a ord t = true

let rec search_ticks (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : GTot nat
  =
  match t with
  | Leaf -> 0
  | Node l k r ->
      let c = key `ord.TO.compare` k in
      if lt c then 1 + search_ticks a ord l key
      else if gt c then 1 + search_ticks a ord r key
      else 1

let rec insert_ticks (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : GTot nat
  =
  match t with
  | Leaf -> 0
  | Node l k r ->
      let c = key `ord.TO.compare` k in
      if lt c then 1 + insert_ticks a ord l key
      else if gt c then 1 + insert_ticks a ord r key
      else 1

let rec delete_ticks (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : GTot nat
  =
  match t with
  | Leaf -> 0
  | Node l k r ->
      let c = key `ord.TO.compare` k in
      if lt c then
        1 + delete_ticks a ord l key
      else if gt c then
        1 + delete_ticks a ord r key
      else
        match l, r with
        | Leaf, Leaf -> 1
        | Leaf, _ -> 1
        | _, Leaf -> 1
        | _, _ ->
            match minimum_model a r with
            | Some successor -> 1 + delete_ticks a ord r successor
            | None -> 1

let rec search_ticks_bounded (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : Lemma (ensures search_ticks a ord t key <= height a t)
  =
  match t with
  | Leaf -> ()
  | Node l k r ->
      let c = key `ord.TO.compare` k in
      if lt c then search_ticks_bounded a ord l key
      else if gt c then search_ticks_bounded a ord r key

let rec insert_ticks_bounded (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : Lemma (ensures insert_ticks a ord t key <= height a t)
  =
  match t with
  | Leaf -> ()
  | Node l k r ->
      let c = key `ord.TO.compare` k in
      if lt c then insert_ticks_bounded a ord l key
      else if gt c then insert_ticks_bounded a ord r key

let rec delete_ticks_bounded (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : Lemma (ensures delete_ticks a ord t key <= SC.bst_delete_bound (height a t) (size a t))
  =
  match t with
  | Leaf -> ()
  | Node l k r ->
      let c = key `ord.TO.compare` k in
      if lt c then delete_ticks_bounded a ord l key
      else if gt c then delete_ticks_bounded a ord r key
      else
        match l, r with
        | Leaf, Leaf -> ()
        | Leaf, _ -> ()
        | _, Leaf -> ()
        | _, _ ->
            match minimum_model a r with
            | Some successor -> delete_ticks_bounded a ord r successor
            | None -> ()

// ============================================================
// BST Validity Lemmas
// ============================================================

// Expose transitivity and flip axioms from total_order to SMT
let reveal_ord (a:Type0) (ord:erased (TO.total_order a))
  : Lemma (
      (forall (x y z:a). {:pattern ord.TO.compare x y; ord.TO.compare y z}
        lt (ord.TO.compare x y) /\ lt (ord.TO.compare y z) ==> lt (ord.TO.compare x z)) /\
      (forall (x y:a). {:pattern ord.TO.compare x y}
        ord.TO.compare x y == TO.flip_order (ord.TO.compare y x)))
  = let _ = ord.TO.properties in ()

let flip_gt_lt (a:Type0) (ord:erased (TO.total_order a)) (x y:a)
  : Lemma (requires gt_ord a ord x y = true) (ensures lt_ord a ord y x = true)
  = reveal_ord a ord

let flip_lt_gt (a:Type0) (ord:erased (TO.total_order a)) (x y:a)
  : Lemma (requires lt_ord a ord x y = true) (ensures gt_ord a ord y x = true)
  = reveal_ord a ord

let compare_eq_is_eq (a:Type0) (ord:erased (TO.total_order a)) (x y:a)
  : Lemma (requires eq (x `ord.TO.compare` y)) (ensures x == y)
  = let _ = ord.TO.properties in ()

let compare_eq_of_eq (a:Type0) (ord:erased (TO.total_order a)) (x y:a)
  : Lemma (requires x == y) (ensures eq (x `ord.TO.compare` y) = true)
  = let _ = ord.TO.properties in ()

let rec find_model_some_eq (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : Lemma
      (requires Some? (find_model a ord t key))
      (ensures Some?.v (find_model a ord t key) == key)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node l k r ->
      let c = key `ord.TO.compare` k in
      if lt c then find_model_some_eq a ord l key
      else if gt c then find_model_some_eq a ord r key
      else ()

let find_empty (a:Type0) (ord:erased (TO.total_order a)) (key:a)
  : Lemma (ensures find_model a ord (empty_model a) key == None)
  = ()

let rec find_insert_hit (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : Lemma
      (requires valid a ord t)
      (ensures find_model a ord (insert_model a ord t key) key == Some key)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node l k r ->
      let c = key `ord.TO.compare` k in
      if lt c then find_insert_hit a ord l key
      else if gt c then find_insert_hit a ord r key
      else ()

let rec find_insert_other (a:Type0) (ord:erased (TO.total_order a)) (t:bst a)
  (inserted key:a)
  : Lemma
      (requires valid a ord t /\ SC.same_key a ord key inserted = false)
      (ensures find_model a ord (insert_model a ord t inserted) key == find_model a ord t key)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node l k r ->
      let ci = inserted `ord.TO.compare` k in
      let ck = key `ord.TO.compare` k in
      if lt ci then begin
        if lt ck then find_insert_other a ord l inserted key
      end else if gt ci then begin
        if gt ck then find_insert_other a ord r inserted key
      end

let rec find_none_all_lt (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : Lemma
      (requires all_lt a ord t key = true)
      (ensures find_model a ord t key == None)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node l k r ->
      find_none_all_lt a ord l key;
      find_none_all_lt a ord r key

let rec find_none_all_gt (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : Lemma
      (requires all_gt a ord t key = true)
      (ensures find_model a ord t key == None)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node l k r ->
      find_none_all_gt a ord l key;
      find_none_all_gt a ord r key

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec all_lt_weaken (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (b1 b2:a)
  : Lemma (requires all_lt a ord t b1 = true /\ lt_ord a ord b1 b2 = true)
          (ensures all_lt a ord t b2 = true)
          (decreases t)
  = reveal_ord a ord;
    match t with | Leaf -> () | Node l _ r ->
      all_lt_weaken a ord l b1 b2; all_lt_weaken a ord r b1 b2

let rec all_gt_weaken (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (b1 b2:a)
  : Lemma (requires all_gt a ord t b1 = true /\ gt_ord a ord b1 b2 = true)
          (ensures all_gt a ord t b2 = true)
          (decreases t)
  = reveal_ord a ord;
    match t with | Leaf -> () | Node l _ r ->
      all_gt_weaken a ord l b1 b2; all_gt_weaken a ord r b1 b2
#pop-options

// A non-empty tree always has a minimum
let rec minimum_nonempty (a:Type0) (t:bst a)
  : Lemma (requires Node? t) (ensures Some? (minimum_model a t))
          (decreases t)
  = match t with
    | Node Leaf _ _ -> ()
    | Node l _ _ -> minimum_nonempty a l

// The minimum element of t satisfies every all_lt bound
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec minimum_in_all_lt (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (bound:a)
  : Lemma (requires all_lt a ord t bound = true /\ Some? (minimum_model a t))
          (ensures lt_ord a ord (Some?.v (minimum_model a t)) bound = true)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node Leaf _ _ -> ()
    | Node l _ _ ->
        minimum_nonempty a l;
        minimum_in_all_lt a ord l bound

// The minimum element of t satisfies every all_gt bound
let rec minimum_gt_bound (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (bound:a)
  : Lemma (requires all_gt a ord t bound = true /\ Some? (minimum_model a t))
          (ensures gt_ord a ord (Some?.v (minimum_model a t)) bound = true)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node Leaf _ _ -> ()
    | Node l _ _ ->
        minimum_nonempty a l;
        minimum_gt_bound a ord l bound
#pop-options

let rec find_minimum_hit (a:Type0) (ord:erased (TO.total_order a)) (t:bst a)
  : Lemma
      (requires is_bst a ord t = true /\ Some? (minimum_model a t))
      (ensures find_model a ord t (Some?.v (minimum_model a t)) ==
               Some (Some?.v (minimum_model a t)))
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node Leaf k r ->
      compare_eq_of_eq a ord k k
  | Node l k r ->
      minimum_nonempty a l;
      minimum_in_all_lt a ord l k;
      find_minimum_hit a ord l

let rec all_gt_of_lt_min (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : Lemma
      (requires is_bst a ord t = true /\
                Some? (minimum_model a t) /\
                lt_ord a ord key (Some?.v (minimum_model a t)) = true)
      (ensures all_gt a ord t key = true)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node Leaf k r ->
      flip_lt_gt a ord key k;
      all_gt_weaken a ord r k key
  | Node l k r ->
      minimum_nonempty a l;
      minimum_in_all_lt a ord l k;
      all_gt_of_lt_min a ord l key;
      assert (lt_ord a ord key k = true);
      flip_lt_gt a ord key k;
      all_gt_weaken a ord r k key

// Insert preserves all_lt/all_gt bounds
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec insert_all_lt (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key bound:a)
  : Lemma (requires all_lt a ord t bound = true /\ lt_ord a ord key bound = true)
          (ensures all_lt a ord (insert_model a ord t key) bound = true)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node l k r ->
        let c = key `ord.TO.compare` k in
        if lt c then insert_all_lt a ord l key bound
        else if gt c then insert_all_lt a ord r key bound
        else ()

let rec insert_all_gt (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key bound:a)
  : Lemma (requires all_gt a ord t bound = true /\ gt_ord a ord key bound = true)
          (ensures all_gt a ord (insert_model a ord t key) bound = true)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node l k r ->
        let c = key `ord.TO.compare` k in
        if lt c then insert_all_gt a ord l key bound
        else if gt c then insert_all_gt a ord r key bound
        else ()
#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 15"
let rec insert_valid_lemma (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : Lemma (requires is_bst a ord t = true)
          (ensures is_bst a ord (insert_model a ord t key) = true)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node l k r ->
        reveal_ord a ord;
        let c = key `ord.TO.compare` k in
        if lt c then begin
          insert_valid_lemma a ord l key;
          insert_all_lt a ord l key k
        end else if gt c then begin
          insert_valid_lemma a ord r key;
          insert_all_gt a ord r key k
        end else ()
#pop-options

// After deleting the minimum of t, all remaining elements are > minimum
#push-options "--fuel 2 --ifuel 2 --z3rlimit 15"
let rec del_all_gt_min (a:Type0) (ord:erased (TO.total_order a)) (t:bst a)
  : Lemma (requires is_bst a ord t = true /\ Some? (minimum_model a t))
          (ensures (let m = Some?.v (minimum_model a t) in
                    all_gt a ord (delete_model a ord t m) m = true))
          (decreases t)
  = reveal_ord a ord;
    match t with
    | Leaf -> ()
    | Node Leaf k r -> ()   // delete returns r; all_gt r k comes from is_bst t
    | Node l k r ->
        minimum_nonempty a l;
        let m = Some?.v (minimum_model a l) in
        minimum_in_all_lt a ord l k;    // lt_ord m k
        flip_lt_gt a ord m k;           // gt_ord k m
        del_all_gt_min a ord l;         // all_gt (delete_model l m) m  (IH on l)
        all_gt_weaken a ord r k m       // all_gt r m  (since all_gt r k and gt_ord k m)
#pop-options

// Delete preserves all_lt/all_gt bounds
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let rec delete_all_lt (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key bound:a)
  : Lemma (requires is_bst a ord t = true /\ all_lt a ord t bound = true)
          (ensures all_lt a ord (delete_model a ord t key) bound = true)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node l k r ->
        let c = key `ord.TO.compare` k in
        if lt c then delete_all_lt a ord l key bound
        else if gt c then delete_all_lt a ord r key bound
        else
          match l with
          | Leaf -> ()   // delete returns r (or Leaf); all_lt r bound from all_lt t bound
          | _ ->
              match r with
              | Leaf -> ()   // delete returns l; all_lt l bound from all_lt t bound
              | _ ->
                  match minimum_model a r with
                  | None -> ()   // delete returns t unchanged
                  | Some successor ->
                      // delete returns Node l successor (delete_model r successor)
                      minimum_in_all_lt a ord r bound;      // lt_ord successor bound
                      delete_all_lt a ord r successor bound  // all_lt (delete_model r successor) bound

let rec delete_all_gt (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key bound:a)
  : Lemma (requires is_bst a ord t = true /\ all_gt a ord t bound = true)
          (ensures all_gt a ord (delete_model a ord t key) bound = true)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node l k r ->
        let c = key `ord.TO.compare` k in
        if lt c then delete_all_gt a ord l key bound
        else if gt c then delete_all_gt a ord r key bound
        else
          match l with
          | Leaf -> ()
          | _ ->
              match r with
              | Leaf -> ()
              | _ ->
                  match minimum_model a r with
                  | None -> ()
                  | Some successor ->
                      minimum_gt_bound a ord r bound;        // gt_ord successor bound
                      delete_all_gt a ord r successor bound  // all_gt (delete_model r successor) bound
#pop-options

// Delete preserves BST validity
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let rec delete_valid_lemma (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : Lemma (requires is_bst a ord t = true)
          (ensures is_bst a ord (delete_model a ord t key) = true)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node l k r ->
        reveal_ord a ord;
        let c = key `ord.TO.compare` k in
        if lt c then begin
          delete_valid_lemma a ord l key;
          delete_all_lt a ord l key k
        end else if gt c then begin
          delete_valid_lemma a ord r key;
          delete_all_gt a ord r key k
        end else
          match l with
          | Leaf -> ()   // delete returns r; is_bst r from is_bst t
          | _ ->
              match r with
              | Leaf -> ()   // delete returns l; is_bst l from is_bst t
              | _ ->
                  match minimum_model a r with
                  | None -> ()   // delete returns t unchanged
                  | Some successor ->
                      // delete returns Node l successor (delete_model r successor)
                      delete_valid_lemma a ord r successor;   // is_bst (delete_model r successor)
                      minimum_gt_bound a ord r k;             // gt_ord successor k
                      flip_gt_lt a ord successor k;           // lt_ord k successor
                      all_lt_weaken a ord l k successor;      // all_lt l successor
                      del_all_gt_min a ord r                  // all_gt (delete_model r successor) successor
#pop-options

let rec find_delete_hit (a:Type0) (ord:erased (TO.total_order a)) (t:bst a) (key:a)
  : Lemma
      (requires valid a ord t)
      (ensures find_model a ord (delete_model a ord t key) key == None)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node l k r ->
      let c = key `ord.TO.compare` k in
      if lt c then find_delete_hit a ord l key
      else if gt c then find_delete_hit a ord r key
      else
        match l, r with
        | Leaf, _ ->
            assert (eq c);
            compare_eq_is_eq a ord key k;
            find_none_all_gt a ord r key;
            assert (find_model a ord r key == None)
        | _, Leaf ->
            assert (eq c);
            compare_eq_is_eq a ord key k;
            find_none_all_lt a ord l key;
            assert (find_model a ord l key == None)
        | _, _ ->
            assert (eq c);
            compare_eq_is_eq a ord key k;
            minimum_nonempty a r;
            match minimum_model a r with
            | None -> ()
            | Some successor ->
                minimum_gt_bound a ord r key;
                flip_gt_lt a ord successor key;
                find_none_all_lt a ord l key;
                assert (lt_ord a ord key successor = true);
                assert (find_model a ord l key == None);
                assert (find_model a ord (Node l successor (delete_model a ord r successor)) key == None)

let rec find_delete_other (a:Type0) (ord:erased (TO.total_order a)) (t:bst a)
  (deleted key:a)
  : Lemma
      (requires valid a ord t /\ SC.same_key a ord key deleted = false)
      (ensures find_model a ord (delete_model a ord t deleted) key == find_model a ord t key)
      (decreases t)
  =
  reveal_ord a ord;
  match t with
  | Leaf -> ()
  | Node l k r ->
      let cd = deleted `ord.TO.compare` k in
      let ck = key `ord.TO.compare` k in
      if lt cd then begin
        if lt ck then find_delete_other a ord l deleted key
      end else if gt cd then begin
        if gt ck then find_delete_other a ord r deleted key
      end else begin
        assert (eq cd);
        compare_eq_is_eq a ord deleted k;
        if lt ck then begin
          match l, r with
          | Leaf, _ ->
              flip_lt_gt a ord key k;
              all_gt_weaken a ord r k key;
              find_none_all_gt a ord r key
          | _, Leaf -> ()
          | _, _ ->
              minimum_nonempty a r;
              match minimum_model a r with
              | None -> ()
              | Some successor ->
                  minimum_gt_bound a ord r k;
                  flip_gt_lt a ord successor k;
                  assert (lt_ord a ord key successor = true)
        end else if gt ck then begin
          match l, r with
          | Leaf, _ -> ()
          | _, Leaf ->
              flip_gt_lt a ord key k;
              all_lt_weaken a ord l k key;
              find_none_all_lt a ord l key
          | _, _ ->
              minimum_nonempty a r;
              match minimum_model a r with
              | None -> ()
              | Some successor ->
                  let cs = key `ord.TO.compare` successor in
                  if lt cs then begin
                    flip_gt_lt a ord key k;
                    all_lt_weaken a ord l k key;
                    find_none_all_lt a ord l key;
                    all_gt_of_lt_min a ord r key;
                    find_none_all_gt a ord r key
                  end else if gt cs then begin
                    find_delete_other a ord r successor key
                  end else begin
                    assert (eq cs);
                    compare_eq_is_eq a ord key successor;
                    find_minimum_hit a ord r
                  end
        end else begin
          assert (eq ck);
          compare_eq_is_eq a ord key k;
          compare_eq_of_eq a ord key deleted;
          assert (SC.same_key a ord key deleted = true)
        end
      end

let rec bst_subtree (a:Type0) (ct:bst_ptr a) (ft:bst a) (parent:bst_ptr a)
  : Tot slprop (decreases ft)
  =
  match ft with
  | Leaf -> pure (ct == None #(bst_node_ptr a))
  | Node l k r ->
      exists* (bp:bst_node_ptr a) (node:bst_node a).
        pure (ct == Some bp) **
        (bp |-> node) **
        pure (node.key == k /\ node.p == parent) **
        bst_subtree a node.left l (Some bp) **
        bst_subtree a node.right r (Some bp)

let owns (a:Type0) (tree:bst_ptr a) (model:bst a) : slprop =
  bst_subtree a tree model (None #(bst_node_ptr a))

ghost fn elim_bst_leaf (a:Type0) (x:bst_ptr a) (#parent:bst_ptr a)
  requires bst_subtree a x Leaf parent
  ensures pure (x == None #(bst_node_ptr a))
{
  unfold (bst_subtree a x Leaf parent)
}

ghost fn intro_bst_leaf (a:Type0) (x:bst_ptr a) (parent:bst_ptr a)
  requires pure (x == None #(bst_node_ptr a))
  ensures bst_subtree a x Leaf parent
{
  fold (bst_subtree a x Leaf parent)
}

ghost fn intro_bst_node (a:Type0) (ct:bst_ptr a) (bp:bst_node_ptr a)
  (#node:bst_node a) (#lt #rt:bst a)
  requires
    (bp |-> node) **
    bst_subtree a node.left lt (Some bp) **
    bst_subtree a node.right rt (Some bp) **
    pure (ct == Some bp)
  ensures bst_subtree a ct (Node lt node.key rt) node.p
{
  fold (bst_subtree a ct (Node lt node.key rt) node.p)
}

[@@no_mkeys]
let bst_cases (a:Type0) (x:bst_ptr a) (ft:bst a) (parent:bst_ptr a) =
  match x with
  | None -> pure (ft == Leaf)
  | Some bp ->
      exists* (node:bst_node a) (lt rt:bst a).
        (bp |-> node) **
        pure (ft == Node lt node.key rt /\ node.p == parent) **
        bst_subtree a node.left lt (Some bp) **
        bst_subtree a node.right rt (Some bp)

ghost fn cases_of_bst (a:Type0) (x:bst_ptr a) (ft:bst a) (parent:bst_ptr a)
  requires bst_subtree a x ft parent
  ensures bst_cases a x ft parent
{
  match ft {
    Leaf -> {
      unfold (bst_subtree a x Leaf parent);
      fold (bst_cases a (None #(bst_node_ptr a)) ft parent);
      rewrite bst_cases a (None #(bst_node_ptr a)) ft parent as bst_cases a x ft parent;
    }
    Node l k r -> {
      unfold (bst_subtree a x (Node l k r) parent);
      with bp node. _;
      fold (bst_cases a (Some bp) ft parent);
      rewrite bst_cases a (Some bp) ft parent as bst_cases a x ft parent;
    }
  }
}

ghost fn bst_case_none (a:Type0) (x:bst_ptr a) (#ft:bst a) (#parent:bst_ptr a)
  preserves bst_subtree a x ft parent
  requires pure (x == None #(bst_node_ptr a))
  ensures pure (ft == Leaf)
{
  rewrite each x as (None #(bst_node_ptr a));
  cases_of_bst a (None #(bst_node_ptr a)) ft parent;
  unfold (bst_cases a);
  intro_bst_leaf a (None #(bst_node_ptr a)) parent;
  rewrite bst_subtree a (None #(bst_node_ptr a)) Leaf parent as bst_subtree a x ft parent
}

ghost fn bst_case_some (a:Type0) (x:bst_ptr a) (bp:bst_node_ptr a)
  (#ft:bst a) (#parent:bst_ptr a)
  requires bst_subtree a x ft parent ** pure (x == Some bp)
  ensures exists* (node:bst_node a) (lt rt:bst a).
    (bp |-> node) **
    bst_subtree a node.left lt (Some bp) **
    bst_subtree a node.right rt (Some bp) **
    pure (ft == Node lt node.key rt /\ node.p == parent)
{
  rewrite each x as (Some bp);
  cases_of_bst a (Some bp) ft parent;
  unfold (bst_cases a)
}

fn create (a:Type0)
  (#ord:erased (TO.total_order a))
  requires emp
  returns tree:bst_ptr a
  ensures owns a tree (empty_model a) ** pure (valid a ord (empty_model a))
{
  let tree : bst_ptr a = None #(bst_node_ptr a);
  intro_bst_leaf a tree (None #(bst_node_ptr a));
  fold (owns a tree (empty_model a));
  tree
}

fn rec free_bst (a:Type0) (tree:bst_ptr a)
  requires bst_subtree a tree 'ft 'parent
  ensures emp
  decreases 'ft
{
  match tree {
    None -> {
      cases_of_bst a (None #(bst_node_ptr a)) 'ft 'parent;
      unfold (bst_cases a)
    }
    Some bp -> {
      bst_case_some a (Some bp) bp;
      let node = !bp;
      free_bst a node.left;
      free_bst a node.right;
      Box.free bp
    }
  }
}

fn dispose (a:Type0)
  (tree:bst_ptr a)
  (#m:erased (bst a))
  requires owns a tree m
  ensures emp
{
  unfold (owns a tree m);
  free_bst a tree
}

fn rec tree_search (a:Type0)
  (tree:bst_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  preserves bst_subtree a tree 'ft 'parent
  requires MR.pts_to ctr #1.0R 'n
  returns result:option a
  ensures exists* ticks.
    MR.pts_to ctr #1.0R ticks **
    pure (result == find_model a ord 'ft key /\
          ticks == reveal 'n + search_ticks a ord 'ft key)
{
  match tree {
    None -> {
      bst_case_none a (None #(bst_node_ptr a));
      rewrite bst_subtree a (None #(bst_node_ptr a)) 'ft 'parent
        as bst_subtree a tree 'ft 'parent;
      None
    }
    Some bp -> {
      bst_case_some a (Some bp) bp;
      let node = !bp;
      let c = iord key node.key;
      if (lt c) {
        let r = tree_search a node.left key ctr #ord iord;
        intro_bst_node a (Some bp) bp;
        with t p. rewrite bst_subtree a (Some bp) t p as bst_subtree a tree 'ft 'parent;
        r
      } else if (gt c) {
        let r = tree_search a node.right key ctr #ord iord;
        intro_bst_node a (Some bp) bp;
        with t p. rewrite bst_subtree a (Some bp) t p as bst_subtree a tree 'ft 'parent;
        r
      } else {
        intro_bst_node a (Some bp) bp;
        with t p. rewrite bst_subtree a (Some bp) t p as bst_subtree a tree 'ft 'parent;
        Some node.key
      }
    }
  }
}

fn new_bst_node (a:Type0) (key:a) (parent:bst_ptr a)
  requires emp
  returns y:bst_ptr a
  ensures bst_subtree a y (Node Leaf key Leaf) parent ** pure (Some? y)
{
  let left_nil : bst_ptr a = None #(bst_node_ptr a);
  let right_nil : bst_ptr a = None #(bst_node_ptr a);
  let bp = Box.alloc ({ key = key; left = left_nil; right = right_nil; p = parent } <: bst_node a);
  intro_bst_leaf a left_nil (Some bp);
  intro_bst_leaf a right_nil (Some bp);
  intro_bst_node a (Some bp) bp;
  Some bp
}

fn rec tree_insert (a:Type0)
  (tree:bst_ptr a)
  (key:a)
  (parent:bst_ptr a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  requires bst_subtree a tree 'ft parent ** MR.pts_to ctr #1.0R 'n
  returns y:bst_ptr a
  ensures exists* ticks.
    bst_subtree a y (insert_model a ord 'ft key) parent **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks == reveal 'n + insert_ticks a ord 'ft key)
{
  match tree {
    None -> {
      bst_case_none a (None #(bst_node_ptr a));
      rewrite bst_subtree a (None #(bst_node_ptr a)) 'ft parent
        as bst_subtree a (None #(bst_node_ptr a)) Leaf parent;
      elim_bst_leaf a (None #(bst_node_ptr a));
      let y = new_bst_node a key parent;
      with t. rewrite bst_subtree a y t parent
        as bst_subtree a y (insert_model a ord 'ft key) parent;
      y
    }
    Some bp -> {
      bst_case_some a (Some bp) bp;
      let node = !bp;
      let c = iord key node.key;
      if (lt c) {
        let new_left = tree_insert a node.left key (Some bp) ctr #ord iord;
        bp := { node with left = new_left };
        intro_bst_node a (Some bp) bp;
        with t p. rewrite bst_subtree a (Some bp) t p
          as bst_subtree a (Some bp) (insert_model a ord 'ft key) parent;
        Some bp
      } else if (gt c) {
        let new_right = tree_insert a node.right key (Some bp) ctr #ord iord;
        bp := { node with right = new_right };
        intro_bst_node a (Some bp) bp;
        with t p. rewrite bst_subtree a (Some bp) t p
          as bst_subtree a (Some bp) (insert_model a ord 'ft key) parent;
        Some bp
      } else {
        intro_bst_node a (Some bp) bp;
        with t p. rewrite bst_subtree a (Some bp) t p
          as bst_subtree a tree (insert_model a ord 'ft key) parent;
        tree
      }
    }
  }
}

fn set_parent_ptr (a:Type0) (child:bst_ptr a) (new_parent:bst_ptr a)
  requires bst_subtree a child 'ft 'old_parent
  ensures bst_subtree a child 'ft new_parent
{
  match child {
    None -> {
      bst_case_none a (None #(bst_node_ptr a));
      rewrite bst_subtree a (None #(bst_node_ptr a)) 'ft 'old_parent
        as bst_subtree a (None #(bst_node_ptr a)) Leaf 'old_parent;
      elim_bst_leaf a (None #(bst_node_ptr a));
      intro_bst_leaf a (None #(bst_node_ptr a)) new_parent;
      rewrite bst_subtree a (None #(bst_node_ptr a)) Leaf new_parent
        as bst_subtree a child 'ft new_parent
    }
    Some bp -> {
      bst_case_some a (Some bp) bp;
      let node = !bp;
      bp := { node with p = new_parent };
      intro_bst_node a (Some bp) bp;
      with t p. rewrite bst_subtree a (Some bp) t p as bst_subtree a child 'ft new_parent
    }
  }
}

ghost fn consume_bst_leaf (a:Type0) (x:bst_ptr a) (#ft:bst a) (#parent:bst_ptr a)
  requires bst_subtree a x ft parent ** pure (x == None #(bst_node_ptr a))
  ensures pure (ft == Leaf)
{
  rewrite each x as (None #(bst_node_ptr a));
  cases_of_bst a (None #(bst_node_ptr a)) ft parent;
  unfold (bst_cases a)
}

ghost fn bst_subtree_some_is_node (a:Type0) (x:bst_ptr a) (bp:bst_node_ptr a)
  (#ft:bst a) (#parent:bst_ptr a)
  preserves bst_subtree a x ft parent
  requires pure (x == Some bp)
  ensures pure (Node? ft)
{
  bst_case_some a x bp;
  intro_bst_node a x bp;
  with t p. rewrite bst_subtree a x t p as bst_subtree a x ft parent
}

fn rec tree_minimum (a:Type0) (tree:bst_ptr a) (bp:bst_node_ptr a)
  preserves bst_subtree a tree 'ft 'parent
  requires pure (tree == Some bp)
  returns result:a
  ensures pure (minimum_model a 'ft == Some result)
{
  rewrite each tree as (Some bp);
  bst_case_some a (Some bp) bp;
  let node = !bp;
  match node.left {
    None -> {
      bst_case_none a node.left;
      intro_bst_node a (Some bp) bp;
      with t p. rewrite bst_subtree a (Some bp) t p as bst_subtree a tree 'ft 'parent;
      node.key
    }
    Some lbp -> {
      let result = tree_minimum a node.left lbp;
      intro_bst_node a (Some bp) bp;
      with t p. rewrite bst_subtree a (Some bp) t p as bst_subtree a tree 'ft 'parent;
      result
    }
  }
}

fn rec tree_delete (a:Type0)
  (tree:bst_ptr a)
  (key:a)
  (parent:bst_ptr a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  requires bst_subtree a tree 'ft parent ** MR.pts_to ctr #1.0R 'n
  returns y:bst_ptr a
  ensures exists* ticks.
    bst_subtree a y (delete_model a ord 'ft key) parent **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks == reveal 'n + delete_ticks a ord 'ft key)
  decreases 'ft
{
  match tree {
    None -> {
      bst_case_none a (None #(bst_node_ptr a));
      rewrite bst_subtree a (None #(bst_node_ptr a)) 'ft parent
        as bst_subtree a (None #(bst_node_ptr a)) Leaf parent;
      rewrite bst_subtree a (None #(bst_node_ptr a)) Leaf parent
        as bst_subtree a (None #(bst_node_ptr a)) (delete_model a ord 'ft key) parent;
      None #(bst_node_ptr a)
    }
    Some bp -> {
      bst_case_some a (Some bp) bp;
      let node = !bp;
      let c = iord key node.key;
      if (lt c) {
        let new_left = tree_delete a node.left key (Some bp) ctr #ord iord;
        bp := { node with left = new_left };
        intro_bst_node a (Some bp) bp;
        with t p. rewrite bst_subtree a (Some bp) t p
          as bst_subtree a (Some bp) (delete_model a ord 'ft key) parent;
        Some bp
      } else if (gt c) {
        let new_right = tree_delete a node.right key (Some bp) ctr #ord iord;
        bp := { node with right = new_right };
        intro_bst_node a (Some bp) bp;
        with t p. rewrite bst_subtree a (Some bp) t p
          as bst_subtree a (Some bp) (delete_model a ord 'ft key) parent;
        Some bp
      } else {
        match node.left {
          None -> {
            consume_bst_leaf a node.left;
            set_parent_ptr a node.right parent;
            Box.free bp;
            with t p. rewrite bst_subtree a node.right t p
              as bst_subtree a node.right (delete_model a ord 'ft key) parent;
            node.right
          }
          Some lbp -> {
            match node.right {
              None -> {
                consume_bst_leaf a node.right;
                set_parent_ptr a node.left parent;
                Box.free bp;
                with t p. rewrite bst_subtree a node.left t p
                  as bst_subtree a node.left (delete_model a ord 'ft key) parent;
                node.left
              }
              Some rbp -> {
                bst_subtree_some_is_node a node.left lbp;
                bst_subtree_some_is_node a node.right rbp;
                let sk = tree_minimum a node.right rbp;
                let new_right = tree_delete a node.right sk (Some bp) ctr #ord iord;
                bp := { node with key = sk; right = new_right };
                intro_bst_node a (Some bp) bp;
                with t p. rewrite bst_subtree a (Some bp) t p
                  as bst_subtree a (Some bp) (delete_model a ord 'ft key) parent;
                Some bp
              }
            }
          }
        }
      }
    }
  }
}

fn search (a:Type0)
  (tree:bst_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  (#m:erased (bst a))
  (#i:erased nat)
  preserves owns a tree m
  requires MR.pts_to ctr #1.0R i ** pure (valid a ord m)
  returns result:option a
  ensures exists* ticks.
    MR.pts_to ctr #1.0R ticks **
    pure (result == find_model a ord m key /\
          ticks <= reveal i + SC.bst_search_bound (height a m) (size a m))
{
  unfold (owns a tree m);
  let result = tree_search a tree key ctr #ord iord;
  with ticks. assert (MR.pts_to ctr #1.0R ticks);
  search_ticks_bounded a ord m key;
  fold (owns a tree m);
  result
}

fn insert (a:Type0)
  (tree:bst_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  (#m:erased (bst a))
  (#i:erased nat)
  requires owns a tree m ** MR.pts_to ctr #1.0R i ** pure (valid a ord m)
  returns tree':bst_ptr a
  ensures exists* ticks.
    owns a tree' (insert_model a ord m key) **
    MR.pts_to ctr #1.0R ticks **
    pure (valid a ord (insert_model a ord m key) /\
          ticks <= reveal i + SC.bst_insert_bound (height a m) (size a m))
{
  unfold (owns a tree m);
  let tree' = tree_insert a tree key (None #(bst_node_ptr a)) ctr #ord iord;
  with ticks. assert (MR.pts_to ctr #1.0R ticks);
  insert_ticks_bounded a ord m key;
  insert_valid_lemma a ord m key;
  fold (owns a tree' (insert_model a ord m key));
  tree'
}

fn delete (a:Type0)
  (tree:bst_ptr a)
  (key:a)
  (ctr:SC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:SC.instrumented_total_order a ord ctr)
  (#m:erased (bst a))
  (#i:erased nat)
  requires owns a tree m ** MR.pts_to ctr #1.0R i ** pure (valid a ord m)
  returns tree':bst_ptr a
  ensures exists* ticks.
    owns a tree' (delete_model a ord m key) **
    MR.pts_to ctr #1.0R ticks **
    pure (valid a ord (delete_model a ord m key) /\
          ticks <= reveal i + SC.bst_delete_bound (height a m) (size a m))
{
  unfold (owns a tree m);
  let tree' = tree_delete a tree key (None #(bst_node_ptr a)) ctr #ord iord;
  with ticks. assert (MR.pts_to ctr #1.0R ticks);
  delete_ticks_bounded a ord m key;
  delete_valid_lemma a ord m key;
  fold (owns a tree' (delete_model a ord m key));
  tree'
}

instance bst_search_structure_instance :
  SC.search_structure
    bst_ptr
    bst
    owns
    valid
    empty_model
    find_model
    insert_model
    delete_model
    height
    size
    SC.bst_search_bound
    SC.bst_insert_bound
    SC.bst_delete_bound
= {
  create = create;
  dispose = dispose;
  search = search;
  insert = insert;
  delete = delete;
}

instance bst_search_model_laws_instance :
  SC.search_model_laws
    bst
    valid
    empty_model
    find_model
    insert_model
    delete_model
= {
  find_empty = find_empty;
  find_insert_hit = find_insert_hit;
  find_insert_other = find_insert_other;
  find_delete_hit = find_delete_hit;
  find_delete_other = find_delete_other;
}
