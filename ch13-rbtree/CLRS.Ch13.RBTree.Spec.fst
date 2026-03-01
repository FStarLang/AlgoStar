(**
 * CLRS Chapter 13: Red-Black Trees — Pure Functional Specification
 *
 * Covers CLRS §13.1–13.4 (properties, rotations, insertion, deletion).
 *
 * Defines:
 *   - Inductive rbtree type with Red/Black colors
 *   - BST ordering predicate (all_lt / all_gt bounds)
 *   - RB invariants: no_red_red, same_black_height, root_black
 *   - Functional search, insert with Okasaki-style balance/fixup
 *   - Functional delete with Kahrs-style balL/balR/fuse
 *   - Minimum/maximum and successor/predecessor operations
 *   - CLRS Theorem 13.1: height ≤ 2·lg(n+1)
 *     via key lemma: node_count ≥ 2^bh - 1
 *   - Correctness: insert/delete preserve membership and BST invariants
 *   - insert_is_rbtree / delete_is_rbtree: RB invariant preservation
 *
 * The balancing approach follows Okasaki, "Red-Black Trees in a
 * Functional Setting", Journal of Functional Programming, 1999.
 *
 * All proofs are fully verified — no admits.
 *)
module CLRS.Ch13.RBTree.Spec

open FStar.Mul

(*** Basic Definitions ***)

let max (a b: nat) : nat = if a >= b then a else b

type color = | Red | Black

type rbtree =
  | Leaf : rbtree
  | Node : c:color -> l:rbtree -> v:int -> r:rbtree -> rbtree

(*** Tree Metrics ***)

let rec height (t: rbtree) : nat =
  match t with
  | Leaf -> 0
  | Node _ l _ r -> 1 + max (height l) (height r)

let rec node_count (t: rbtree) : nat =
  match t with
  | Leaf -> 0
  | Node _ l _ r -> 1 + node_count l + node_count r

// Black-height: number of black nodes on path to leaf, not counting self.
// Leaf (NIL) has bh 0.
let rec bh (t: rbtree) : nat =
  match t with
  | Leaf -> 0
  | Node c l _ _ ->
    if c = Black then 1 + bh l else bh l

(*** RB Properties ***)

let is_root_black (t: rbtree) : bool =
  match t with
  | Leaf -> true
  | Node c _ _ _ -> c = Black

// No consecutive red nodes
let rec no_red_red (t: rbtree) : bool =
  match t with
  | Leaf -> true
  | Node c l _ r ->
    (if c = Red then
       (match l with Leaf -> true | Node cl _ _ _ -> cl = Black) &&
       (match r with Leaf -> true | Node cr _ _ _ -> cr = Black)
     else true) &&
    no_red_red l && no_red_red r

// All root-to-leaf paths have same number of black nodes
let rec same_bh (t: rbtree) : bool =
  match t with
  | Leaf -> true
  | Node _ l _ r -> bh l = bh r && same_bh l && same_bh r

let is_rbtree (t: rbtree) : bool =
  is_root_black t && no_red_red t && same_bh t

(*** Membership and BST ***)

let rec mem (x: int) (t: rbtree) : bool =
  match t with
  | Leaf -> false
  | Node _ l v r -> x = v || mem x l || mem x r

// All keys in tree < bound
let rec all_lt (t: rbtree) (bound: int) : bool =
  match t with
  | Leaf -> true
  | Node _ l v r -> v < bound && all_lt l bound && all_lt r bound

// All keys in tree > bound
let rec all_gt (t: rbtree) (bound: int) : bool =
  match t with
  | Leaf -> true
  | Node _ l v r -> v > bound && all_gt l bound && all_gt r bound

// BST ordering: all keys in left < v, all keys in right > v
let rec is_bst (t: rbtree) : bool =
  match t with
  | Leaf -> true
  | Node _ l v r ->
    all_lt l v &&
    all_gt r v &&
    is_bst l && is_bst r

(*** Search ***)

let rec search (t: rbtree) (k: int) : option int =
  match t with
  | Leaf -> None
  | Node _ l v r ->
    if k < v then search l k
    else if k > v then search r k
    else Some v

(*** Okasaki-style Balance (Insert Fixup) ***)

// The four rotation cases from Okasaki
let balance (c: color) (l: rbtree) (v: int) (r: rbtree) : rbtree =
  match c, l, r with
  // Left-left: red left child has red left grandchild
  | Black, Node Red (Node Red a x b) y c_, _ ->
    Node Red (Node Black a x b) y (Node Black c_ v r)
  // Left-right: red left child has red right grandchild
  | Black, Node Red a x (Node Red b y c_), _ ->
    Node Red (Node Black a x b) y (Node Black c_ v r)
  // Right-left: red right child has red left grandchild
  | Black, _, Node Red (Node Red b y c_) z d ->
    Node Red (Node Black l v b) y (Node Black c_ z d)
  // Right-right: red right child has red right grandchild
  | Black, _, Node Red b y (Node Red c_ z d) ->
    Node Red (Node Black l v b) y (Node Black c_ z d)
  // No fixup needed
  | _ -> Node c l v r

// Insert helper (may produce red root)
let rec ins (t: rbtree) (k: int) : rbtree =
  match t with
  | Leaf -> Node Red Leaf k Leaf
  | Node c l v r ->
    if k < v then balance c (ins l k) v r
    else if k > v then balance c l v (ins r k)
    else Node c l v r // duplicate

let make_black (t: rbtree) : rbtree =
  match t with
  | Leaf -> Leaf
  | Node _ l v r -> Node Black l v r

let insert (t: rbtree) (k: int) : rbtree =
  make_black (ins t k)

// ========== Balance case classifier ==========
// Used by the Pulse implementation to determine which rotation to apply
// without deep pattern matching on pointers.

type balance_case =
  | BC_LL   // Left-left:   Node Red (Node Red a x b) y c_, _, v, r
  | BC_LR   // Left-right:  Node Red a x (Node Red b y c_), _, v, r
  | BC_RL   // Right-left:  _, Node Red (Node Red b y c_) z d
  | BC_RR   // Right-right: _, Node Red b y (Node Red c_ z d)
  | BC_None // No fixup needed

let classify_balance (c: color) (l: rbtree) (r: rbtree) : balance_case =
  match c, l, r with
  | Black, Node Red (Node Red _ _ _) _ _, _ -> BC_LL
  | Black, Node Red _ _ (Node Red _ _ _), _ -> BC_LR
  | Black, _, Node Red (Node Red _ _ _) _ _ -> BC_RL
  | Black, _, Node Red _ _ (Node Red _ _ _) -> BC_RR
  | _ -> BC_None

// The classifier agrees with balance
let classify_balance_lemma (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma (
    match classify_balance c l r with
    | BC_LL -> (match l with
               | Node Red (Node Red a x b) y c_ -> balance c l v r == Node Red (Node Black a x b) y (Node Black c_ v r)
               | _ -> False)
    | BC_LR -> (match l with
               | Node Red a x (Node Red b y c_) -> balance c l v r == Node Red (Node Black a x b) y (Node Black c_ v r)
               | _ -> False)
    | BC_RL -> (match r with
               | Node Red (Node Red b y c_) z d -> balance c l v r == Node Red (Node Black l v b) y (Node Black c_ z d)
               | _ -> False)
    | BC_RR -> (match r with
               | Node Red b y (Node Red c_ z d) -> balance c l v r == Node Red (Node Black l v b) y (Node Black c_ z d)
               | _ -> False)
    | BC_None -> balance c l v r == Node c l v r)
  = ()

(*** Theorem 13.1: Height Bound ***)

// Key lemma: node_count t >= pow2 (bh t) - 1
#push-options "--fuel 2 --ifuel 0 --z3rlimit 20"
let rec min_nodes_for_bh (t: rbtree)
  : Lemma
    (requires same_bh t /\ no_red_red t)
    (ensures node_count t >= pow2 (bh t) - 1)
    (decreases (height t))
  = match t with
    | Leaf -> ()
    | Node c l _ r ->
      min_nodes_for_bh l;
      min_nodes_for_bh r;
      Math.Lemmas.pow2_plus 1 (bh l)
#pop-options

// bh >= height / 2 (no consecutive reds means at least half the nodes are black)
#push-options "--fuel 2 --ifuel 0 --z3rlimit 20"
// For red-rooted subtrees, the bound is different, so we remove this lemma
// and use bh_height_bound below which handles both colors.
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
// For any valid subtree, height <= 2*bh + (if Red then 1 else 0)
let color_bonus (t: rbtree) : nat =
  match t with
  | Leaf -> 0
  | Node c _ _ _ -> if c = Red then 1 else 0

let rec bh_height_bound (t: rbtree)
  : Lemma
    (requires no_red_red t /\ same_bh t)
    (ensures height t <= 2 * bh t + color_bonus t)
    (decreases (height t))
  = match t with
    | Leaf -> ()
    | Node c l _ r ->
      bh_height_bound l;
      bh_height_bound r
#pop-options

// For a full rbtree (root is black): height <= 2*bh
let rbtree_height_le_2bh (t: rbtree)
  : Lemma
    (requires is_rbtree t /\ Node? t)
    (ensures height t <= 2 * bh t)
  = bh_height_bound t

// log2 floor for positive integers
let rec log2_floor (n: pos) : Tot nat (decreases n) =
  if n = 1 then 0
  else 1 + log2_floor (n / 2)

// pow2(log2_floor n) <= n
#push-options "--fuel 2 --ifuel 0 --z3rlimit 20"
let rec pow2_log2_le (n: pos)
  : Lemma (ensures pow2 (log2_floor n) <= n)
    (decreases n)
  = if n = 1 then ()
    else begin
      pow2_log2_le (n / 2);
      Math.Lemmas.pow2_plus 1 (log2_floor (n / 2))
    end
#pop-options

// if n >= pow2 k then log2_floor n >= k
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let rec log2_floor_ge (n: pos) (k: nat)
  : Lemma
    (requires n >= pow2 k)
    (ensures log2_floor n >= k)
    (decreases k)
  = if k = 0 then ()
    else begin
      Math.Lemmas.pow2_plus 1 (k - 1);
      // pow2 k = 2 * pow2 (k-1), n >= 2 * pow2 (k-1), so n >= 2, so n/2 >= pow2(k-1)
      assert (n >= 2);
      assert (n / 2 >= pow2 (k - 1));
      log2_floor_ge (n / 2) (k - 1)
    end
#pop-options

// CLRS Theorem 13.1: height <= 2 * log2_floor(n + 1)
let height_bound_theorem (t: rbtree)
  : Lemma
    (requires is_rbtree t /\ node_count t >= 1)
    (ensures height t <= 2 * log2_floor (node_count t + 1))
  = bh_height_bound t;
    min_nodes_for_bh t;
    // node_count t >= pow2(bh t) - 1, so node_count t + 1 >= pow2(bh t)
    // node_count t + 1 is a pos
    log2_floor_ge (node_count t + 1) (bh t);
    // log2_floor(n+1) >= bh t
    // For black root: height t <= 2 * bh t <= 2 * log2_floor(n+1)
    // For Leaf case: excluded by node_count >= 1
    // Must be Node with Black root (is_rbtree)
    ()

(*** Insert Correctness ***)

// balance preserves membership
#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let balance_mem (c: color) (l: rbtree) (v: int) (r: rbtree) (k: int)
  : Lemma (ensures mem k (balance c l v r) <==> (k = v || mem k l || mem k r))
  = ()
#pop-options

// ins preserves membership and adds new key
#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let rec ins_mem (t: rbtree) (k: int) (x: int)
  : Lemma
    (ensures mem x (ins t k) <==> (x = k || mem x t))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        ins_mem l k x;
        balance_mem c (ins l k) v r x
      end else if k > v then begin
        ins_mem r k x;
        balance_mem c l v (ins r k) x
      end else ()
#pop-options

let insert_mem (t: rbtree) (k: int) (x: int)
  : Lemma (ensures mem x (insert t k) <==> (x = k || mem x t))
  = ins_mem t k x

// balance preserves all_lt / all_gt bounds
#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let balance_all_lt (c: color) (l: rbtree) (v: int) (r: rbtree) (bound: int)
  : Lemma 
    (requires all_lt l bound /\ all_lt r bound /\ v < bound)
    (ensures all_lt (balance c l v r) bound)
  = ()

let balance_all_gt (c: color) (l: rbtree) (v: int) (r: rbtree) (bound: int)
  : Lemma 
    (requires all_gt l bound /\ all_gt r bound /\ v > bound)
    (ensures all_gt (balance c l v r) bound)
  = ()
#pop-options

// ins preserves all_lt / all_gt when new key satisfies bound
#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let rec ins_all_lt (t: rbtree) (k: int) (bound: int)
  : Lemma
    (requires all_lt t bound /\ k < bound)
    (ensures all_lt (ins t k) bound)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        ins_all_lt l k bound;
        balance_all_lt c (ins l k) v r bound
      end else if k > v then begin
        ins_all_lt r k bound;
        balance_all_lt c l v (ins r k) bound
      end else ()

let rec ins_all_gt (t: rbtree) (k: int) (bound: int)
  : Lemma
    (requires all_gt t bound /\ k > bound)
    (ensures all_gt (ins t k) bound)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        ins_all_gt l k bound;
        balance_all_gt c (ins l k) v r bound
      end else if k > v then begin
        ins_all_gt r k bound;
        balance_all_gt c l v (ins r k) bound
      end else ()
#pop-options

// Transitivity: all_lt t b1 /\ b1 < b2 ==> all_lt t b2
let rec all_lt_weaken (t: rbtree) (b1 b2: int)
  : Lemma
    (requires all_lt t b1 /\ b1 <= b2)
    (ensures all_lt t b2)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l _ r -> all_lt_weaken l b1 b2; all_lt_weaken r b1 b2

let rec all_gt_weaken (t: rbtree) (b1 b2: int)
  : Lemma
    (requires all_gt t b1 /\ b2 <= b1)
    (ensures all_gt t b2)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l _ r -> all_gt_weaken l b1 b2; all_gt_weaken r b1 b2


// ins preserves BST ordering
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let balance_is_bst (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires is_bst l /\ is_bst r /\ all_lt l v /\ all_gt r v)
    (ensures is_bst (balance c l v r))
  = match c, l, r with
    | Black, Node Red (Node Red a x b) y c_, _ ->
      all_lt_weaken a x y;
      all_gt_weaken r v y
    | Black, Node Red a x (Node Red b y c_), _ ->
      all_lt_weaken a x y;
      all_gt_weaken r v y
    | Black, _, Node Red (Node Red b y c_) z d ->
      all_lt_weaken l v y;
      all_gt_weaken d z y
    | Black, _, Node Red b y (Node Red c_ z d) ->
      all_lt_weaken l v y
    | _ -> ()

let rec ins_preserves_bst (t: rbtree) (k: int)
  : Lemma
    (requires is_bst t)
    (ensures is_bst (ins t k))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        ins_preserves_bst l k;
        ins_all_lt l k v;
        balance_is_bst c (ins l k) v r
      end else if k > v then begin
        ins_preserves_bst r k;
        ins_all_gt r k v;
        balance_is_bst c l v (ins r k)
      end else ()
#pop-options

let insert_preserves_bst (t: rbtree) (k: int)
  : Lemma
    (requires is_bst t)
    (ensures is_bst (insert t k))
  = ins_preserves_bst t k

(*** Insert Preserves RB Properties ***)

// balance preserves same_bh
#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let balance_same_bh (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires same_bh l /\ same_bh r /\ bh l = bh r)
    (ensures same_bh (balance c l v r))
  = ()
#pop-options

// balance preserves bh value  
#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let balance_bh (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires same_bh l /\ same_bh r /\ bh l = bh r)
    (ensures bh (balance c l v r) = bh (Node c l v r))
  = ()
#pop-options

// balance on a Black parent produces a Red root (when fixup fires) or keeps color
// The key insight: balance only fires when c = Black and there's a red-red violation.
// When it fires, it produces a Red root with two Black children — no_red_red holds.
// When it doesn't fire, it just wraps as Node c l v r.

// ins produces a tree where no_red_red holds everywhere except possibly at the root
let almost_no_red_red (t: rbtree) : bool =
  match t with
  | Leaf -> true
  | Node _ l _ r -> no_red_red l && no_red_red r

#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let balance_restores_no_red_red_left (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires c = Black /\ almost_no_red_red l /\ no_red_red r)
    (ensures no_red_red (balance c l v r))
  = match l with
    | Node Red (Node Red _ _ _) _ _ -> ()  // BC_LL
    | Node Red _ _ (Node Red _ _ _) -> ()  // BC_LR
    | _ -> ()                               // BC_None (no right-side rotation since r is no_red_red)

let balance_restores_no_red_red_right (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires c = Black /\ no_red_red l /\ almost_no_red_red r)
    (ensures no_red_red (balance c l v r))
  = match r with
    | Node Red (Node Red _ _ _) _ _ -> ()  // BC_RL
    | Node Red _ _ (Node Red _ _ _) -> ()  // BC_RR
    | _ -> ()                               // BC_None

// Red parent: balance is identity when no fixup patterns match, 
// so result is almost_no_red_red (children are ok, root might not be)
let balance_red_almost (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires no_red_red l /\ no_red_red r)
    (ensures almost_no_red_red (balance Red l v r))
  = ()
#pop-options

// ins maintains same_bh, preserves bh, and has almost_no_red_red
#push-options "--fuel 3 --ifuel 1 --z3rlimit 30"
let rec ins_properties (t: rbtree) (k: int)
  : Lemma
    (requires same_bh t /\ no_red_red t)
    (ensures same_bh (ins t k) /\
             bh (ins t k) = bh t /\
             almost_no_red_red (ins t k) /\
             (Node? t /\ Black? (Node?.c t) ==> no_red_red (ins t k)))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        ins_properties l k;
        balance_same_bh c (ins l k) v r;
        balance_bh c (ins l k) v r;
        if c = Black then
          balance_restores_no_red_red_left c (ins l k) v r
        else
          balance_red_almost (ins l k) v r
      end else if k > v then begin
        ins_properties r k;
        balance_same_bh c l v (ins r k);
        balance_bh c l v (ins r k);
        if c = Black then
          balance_restores_no_red_red_right c l v (ins r k)
        else
          balance_red_almost l v (ins r k)
      end else ()
#pop-options

// insert maintains all RB properties
let insert_is_rbtree (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t)
    (ensures is_rbtree (insert t k))
  = ins_properties t k

(*** Minimum / Maximum ***)

// Find the minimum key in a non-empty BST
let rec minimum (t: rbtree{Node? t}) : int =
  match t with
  | Node _ Leaf v _ -> v
  | Node _ l _ _ -> minimum l

// Find the maximum key in a non-empty BST
let rec maximum (t: rbtree{Node? t}) : int =
  match t with
  | Node _ _ v Leaf -> v
  | Node _ _ _ r -> maximum r

// minimum is a member of the tree
let rec minimum_mem (t: rbtree{Node? t})
  : Lemma (ensures mem (minimum t) t)
    (decreases t)
  = match t with
    | Node _ Leaf v _ -> ()
    | Node _ l _ _ -> minimum_mem l

// maximum is a member of the tree
let rec maximum_mem (t: rbtree{Node? t})
  : Lemma (ensures mem (maximum t) t)
    (decreases t)
  = match t with
    | Node _ _ v Leaf -> ()
    | Node _ _ _ r -> maximum_mem r

// Helper: all_gt r v /\ mem x r ==> x > v
let rec all_gt_mem (t: rbtree) (bound: int) (x: int)
  : Lemma
    (requires all_gt t bound /\ mem x t)
    (ensures x > bound)
    (decreases t)
  = match t with
    | Node _ l v r ->
      if x = v then ()
      else if mem x l then all_gt_mem l bound x
      else all_gt_mem r bound x

// Helper: all_lt l v /\ mem x l ==> x < v
let rec all_lt_mem (t: rbtree) (bound: int) (x: int)
  : Lemma
    (requires all_lt t bound /\ mem x t)
    (ensures x < bound)
    (decreases t)
  = match t with
    | Node _ l v r ->
      if x = v then ()
      else if mem x l then all_lt_mem l bound x
      else all_lt_mem r bound x

// minimum is <= all keys in a BST
let rec minimum_is_min (t: rbtree{Node? t}) (x: int)
  : Lemma
    (requires is_bst t /\ mem x t)
    (ensures minimum t <= x)
    (decreases t)
  = match t with
    | Node _ Leaf v r ->
      if x = v then ()
      else all_gt_mem r v x
    | Node _ l v r ->
      if x = v then begin
        minimum_mem l;
        all_lt_mem l v (minimum l)
      end
      else if mem x l then
        minimum_is_min l x
      else begin
        minimum_mem l;
        all_lt_mem l v (minimum l);
        all_gt_mem r v x
      end

// maximum is >= all keys in a BST
let rec maximum_is_max (t: rbtree{Node? t}) (x: int)
  : Lemma
    (requires is_bst t /\ mem x t)
    (ensures maximum t >= x)
    (decreases t)
  = match t with
    | Node _ l v Leaf ->
      if x = v then ()
      else all_lt_mem l v x
    | Node _ l v r ->
      if x = v then begin
        maximum_mem r;
        all_gt_mem r v (maximum r)
      end
      else if mem x r then
        maximum_is_max r x
      else begin
        maximum_mem r;
        all_gt_mem r v (maximum r);
        all_lt_mem l v x
      end

// Helper: in a BST, if all_gt r v and k <= v, then k is not in r
let rec bst_lt_not_mem (t: rbtree) (bound: int) (k: int)
  : Lemma
    (requires all_gt t bound /\ k <= bound)
    (ensures mem k t = false)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l v r -> bst_lt_not_mem l bound k; bst_lt_not_mem r bound k

// Helper: in a BST, if all_lt l v and k >= v, then k is not in l
let rec bst_gt_not_mem (t: rbtree) (bound: int) (k: int)
  : Lemma
    (requires all_lt t bound /\ k >= bound)
    (ensures mem k t = false)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l v r -> bst_gt_not_mem l bound k; bst_gt_not_mem r bound k

(*** Successor / Predecessor — CLRS §12.2 ***)

// Successor: smallest key strictly greater than k.
// Searches from root (no parent pointers in the pure spec).
let rec successor (t: rbtree) (k: int) : option int =
  match t with
  | Leaf -> None
  | Node _ l v r ->
    if k < v then
      (match successor l k with
       | Some s -> Some s
       | None -> Some v)
    else
      successor r k

// Predecessor: largest key strictly less than k.
let rec predecessor (t: rbtree) (k: int) : option int =
  match t with
  | Leaf -> None
  | Node _ l v r ->
    if k > v then
      (match predecessor r k with
       | Some p -> Some p
       | None -> Some v)
    else
      predecessor l k

// Successor correctness: if successor returns Some s, then s > k and s is in the tree
let rec successor_mem (t: rbtree) (k: int)
  : Lemma (ensures (match successor t k with
                     | Some s -> mem s t = true /\ s > k
                     | None -> true))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l v r ->
      if k < v then
        successor_mem l k
      else
        successor_mem r k

// Predecessor correctness: if predecessor returns Some p, then p < k and p is in the tree
let rec predecessor_mem (t: rbtree) (k: int)
  : Lemma (ensures (match predecessor t k with
                     | Some p -> mem p t = true /\ p < k
                     | None -> true))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node _ l v r ->
      if k > v then
        predecessor_mem r k
      else
        predecessor_mem l k

// Successor is the smallest key > k (in a BST)
#push-options "--fuel 3 --ifuel 1 --z3rlimit 50"
let rec successor_is_next (t: rbtree) (k: int) (x: int)
  : Lemma
    (requires is_bst t /\ mem x t = true /\ x > k)
    (ensures (match successor t k with
               | Some s -> s <= x
               | None -> false))
    (decreases t)
  = match t with
    | Node _ l v r ->
      if k < v then begin
        if x < v then begin
          // x is in l (from is_bst: all_gt r v and x < v means x not in r)
          bst_lt_not_mem r v x;
          successor_is_next l k x
        end else if x = v then begin
          // successor l k returns Some s with s in l, hence s < v = x; or None → Some v = x
          successor_mem l k;
          match successor l k with
          | Some s -> all_lt_mem l v s
          | None -> ()
        end else begin
          // x > v, x is in r. successor l k gives Some s < v < x, or None → Some v < x
          successor_mem l k;
          match successor l k with
          | Some s -> all_lt_mem l v s
          | None -> ()
        end
      end else begin
        // k >= v, so x > k >= v, meaning x > v and x must be in r
        if x > v then begin
          bst_gt_not_mem l v x;
          successor_is_next r k x
        end else ()  // x <= v contradicts x > k >= v
      end
#pop-options

// Predecessor is the largest key < k (in a BST)
#push-options "--fuel 3 --ifuel 1 --z3rlimit 50"
let rec predecessor_is_prev (t: rbtree) (k: int) (x: int)
  : Lemma
    (requires is_bst t /\ mem x t = true /\ x < k)
    (ensures (match predecessor t k with
               | Some p -> p >= x
               | None -> false))
    (decreases t)
  = match t with
    | Node _ l v r ->
      if k > v then begin
        if x > v then begin
          bst_gt_not_mem l v x;
          predecessor_is_prev r k x
        end else if x = v then begin
          predecessor_mem r k;
          match predecessor r k with
          | Some p -> all_gt_mem r v p
          | None -> ()
        end else begin
          // x < v, x is in l. predecessor r k gives Some p > v > x, or None → Some v > x
          predecessor_mem r k;
          match predecessor r k with
          | Some p -> all_gt_mem r v p
          | None -> ()
        end
      end else begin
        if x < v then begin
          bst_lt_not_mem r v x;
          predecessor_is_prev l k x
        end else ()
      end
#pop-options

(*** Delete — Kahrs-style functional deletion ***)

// Recolor a black node to red (used in delete rebalancing).
let redden (t: rbtree) : rbtree =
  match t with
  | Node Black l v r -> Node Red l v r
  | _ -> t

// Rebalance after deletion from the left subtree caused a black-height deficit.
let balL (l: rbtree) (v: int) (r: rbtree) : rbtree =
  match l, r with
  | Node Red a x b, _ ->
    Node Red (Node Black a x b) v r
  | _, Node Black b y c ->
    balance Black l v (Node Red b y c)
  | _, Node Red (Node Black b y c) z d ->
    Node Red (Node Black l v b) y (balance Black c z (redden d))
  | _ -> Node Black l v r

// Rebalance after deletion from the right subtree caused a black-height deficit.
let balR (l: rbtree) (v: int) (r: rbtree) : rbtree =
  match l, r with
  | _, Node Red b y c ->
    Node Red l v (Node Black b y c)
  | Node Black a x b, _ ->
    balance Black (Node Red a x b) v r
  | Node Red a x (Node Black b y c), _ ->
    Node Red (balance Black (redden a) x b) y (Node Black c v r)
  | _ -> Node Black l v r

// Fuse two subtrees: merge the children of a deleted node.
let rec fuse (l r: rbtree) : Tot rbtree (decreases (node_count l + node_count r)) =
  match l, r with
  | Leaf, _ -> r
  | _, Leaf -> l
  | Node Red a x b, Node Red c y d ->
    let s = fuse b c in
    (match s with
     | Node Red b' z c' -> Node Red (Node Red a x b') z (Node Red c' y d)
     | _ -> Node Red a x (Node Red s y d))
  | Node Black a x b, Node Black c y d ->
    let s = fuse b c in
    (match s with
     | Node Red b' z c' -> Node Red (Node Black a x b') z (Node Black c' y d)
     | _ -> balL a x (Node Black s y d))
  | Node Red a x b, _ ->
    Node Red a x (fuse b r)
  | _, Node Red c y d ->
    Node Red (fuse l c) y d

// Delete helper: removes key k from tree t.
// Following Kahrs' formulation: when the target child is Black, use balL/balR
// to rebalance (the child's bh decreases by 1). When the child is not Black
// (Red or Leaf), use Node Red to absorb the parent's black level.
let rec del (t: rbtree) (k: int) : Tot rbtree (decreases t) =
  match t with
  | Leaf -> Leaf
  | Node c l v r ->
    if k < v then
      (match l with
       | Node Black _ _ _ -> balL (del l k) v r
       | _ -> Node Red (del l k) v r)
    else if k > v then
      (match r with
       | Node Black _ _ _ -> balR l v (del r k)
       | _ -> Node Red l v (del r k))
    else
      fuse l r

// Top-level delete: del + make root black
let delete (t: rbtree) (k: int) : rbtree =
  make_black (del t k)

(*** Delete Correctness — Membership ***)


// balL preserves membership
#push-options "--fuel 4 --ifuel 2 --z3rlimit 30"
let balL_mem (l: rbtree) (v: int) (r: rbtree) (x: int)
  : Lemma (ensures mem x (balL l v r) <==> (x = v || mem x l || mem x r))
  = match l, r with
    | _, Node Black b y c -> balance_mem Black l v (Node Red b y c) x
    | _, Node Red (Node Black b y c) z d ->
      balance_mem Black c z (redden d) x
    | _ -> ()
#pop-options

// balR preserves membership
#push-options "--fuel 4 --ifuel 2 --z3rlimit 30"
let balR_mem (l: rbtree) (v: int) (r: rbtree) (x: int)
  : Lemma (ensures mem x (balR l v r) <==> (x = v || mem x l || mem x r))
  = match l, r with
    | Node Black a x' b, _ -> balance_mem Black (Node Red a x' b) v r x
    | Node Red a x' (Node Black b y c), _ ->
      balance_mem Black (redden a) x' b x
    | _ -> ()
#pop-options

// fuse preserves membership
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let rec fuse_mem (l r: rbtree) (x: int)
  : Lemma
    (ensures mem x (fuse l r) <==> (mem x l || mem x r))
    (decreases (node_count l + node_count r))
  = match l, r with
    | Leaf, _ -> ()
    | _, Leaf -> ()
    | Node Red a xv b, Node Red c y d ->
      fuse_mem b c x
    | Node Black a xv b, Node Black c y d ->
      fuse_mem b c x;
      (match fuse b c with
       | Node Red _ _ _ -> ()
       | _ -> balL_mem a xv (Node Black (fuse b c) y d) x)
    | Node Red a xv b, _ ->
      fuse_mem b r x
    | _, Node Red c y d ->
      fuse_mem l c x
#pop-options

// del preserves membership (removes exactly k)
#push-options "--fuel 5 --ifuel 3 --z3rlimit 50"
let rec del_mem (t: rbtree) (k: int) (x: int)
  : Lemma
    (requires is_bst t)
    (ensures mem x (del t k) <==> (mem x t && x <> k))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      assert (is_bst l /\ is_bst r);
      if k < v then begin
        del_mem l k x;
        bst_lt_not_mem r v k;
        assert (mem k r = false);
        (match l with
         | Node Black _ _ _ -> balL_mem (del l k) v r x
         | _ -> ())
      end else if k > v then begin
        del_mem r k x;
        bst_gt_not_mem l v k;
        assert (mem k l = false);
        (match r with
         | Node Black _ _ _ -> balR_mem l v (del r k) x
         | _ -> ())
      end else begin
        bst_gt_not_mem l v v;
        bst_lt_not_mem r v v;
        fuse_mem l r x
      end
#pop-options

// delete preserves membership (removes exactly k)
let delete_mem (t: rbtree) (k: int) (x: int)
  : Lemma
    (requires is_bst t)
    (ensures mem x (delete t k) <==> (mem x t && x <> k))
  = del_mem t k x

(*** Delete Correctness — BST Preservation ***)

// balL preserves all_lt / all_gt
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let balL_all_lt (l: rbtree) (v: int) (r: rbtree) (bound: int)
  : Lemma
    (requires all_lt l bound /\ all_lt r bound /\ v < bound)
    (ensures all_lt (balL l v r) bound)
  = match l, r with
    | _, Node Black b y c -> balance_all_lt Black l v (Node Red b y c) bound
    | _, Node Red (Node Black b y c) z d ->
      balance_all_lt Black c z (redden d) bound
    | _ -> ()

let balL_all_gt (l: rbtree) (v: int) (r: rbtree) (bound: int)
  : Lemma
    (requires all_gt l bound /\ all_gt r bound /\ v > bound)
    (ensures all_gt (balL l v r) bound)
  = match l, r with
    | _, Node Black b y c -> balance_all_gt Black l v (Node Red b y c) bound
    | _, Node Red (Node Black b y c) z d ->
      balance_all_gt Black c z (redden d) bound
    | _ -> ()

let balR_all_lt (l: rbtree) (v: int) (r: rbtree) (bound: int)
  : Lemma
    (requires all_lt l bound /\ all_lt r bound /\ v < bound)
    (ensures all_lt (balR l v r) bound)
  = match l, r with
    | Node Black a x b, _ -> balance_all_lt Black (Node Red a x b) v r bound
    | Node Red a x (Node Black b y c), _ ->
      balance_all_lt Black (redden a) x b bound
    | _ -> ()

let balR_all_gt (l: rbtree) (v: int) (r: rbtree) (bound: int)
  : Lemma
    (requires all_gt l bound /\ all_gt r bound /\ v > bound)
    (ensures all_gt (balR l v r) bound)
  = match l, r with
    | Node Black a x b, _ -> balance_all_gt Black (Node Red a x b) v r bound
    | Node Red a x (Node Black b y c), _ ->
      balance_all_gt Black (redden a) x b bound
    | _ -> ()
#pop-options

// balL preserves BST
#push-options "--fuel 5 --ifuel 3 --z3rlimit 80"
let balL_is_bst (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires is_bst l /\ is_bst r /\ all_lt l v /\ all_gt r v)
    (ensures is_bst (balL l v r))
  = match l, r with
    | _, Node Black b y c ->
      balance_is_bst Black l v (Node Red b y c)
    | _, Node Red (Node Black b y c) z d ->
      // Result: Node Red (Node Black l v b) y (balance Black c z (redden d))
      // Establish facts from preconditions
      all_lt_weaken l v y;
      all_gt_weaken d z y;
      balance_is_bst Black c z (redden d);
      balance_all_gt Black c z (redden d) y
    | _ -> ()

let balR_is_bst (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires is_bst l /\ is_bst r /\ all_lt l v /\ all_gt r v)
    (ensures is_bst (balR l v r))
  = match l, r with
    | Node Black a x b, _ ->
      balance_is_bst Black (Node Red a x b) v r
    | Node Red a x (Node Black b y c), _ ->
      all_gt_weaken r v y;
      all_lt_weaken a x y;
      balance_is_bst Black (redden a) x b;
      balance_all_lt Black (redden a) x b y
    | _ -> ()
#pop-options

// fuse preserves all_lt
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let rec fuse_all_lt (l r: rbtree) (bound: int)
  : Lemma
    (requires all_lt l bound /\ all_lt r bound)
    (ensures all_lt (fuse l r) bound)
    (decreases (node_count l + node_count r))
  = match l, r with
    | Leaf, _ -> ()
    | _, Leaf -> ()
    | Node Red a x b, Node Red c y d ->
      fuse_all_lt b c bound
    | Node Black a x b, Node Black c y d ->
      fuse_all_lt b c bound;
      (match fuse b c with
       | Node Red _ _ _ -> ()
       | _ -> balL_all_lt a x (Node Black (fuse b c) y d) bound)
    | Node Red a x b, _ ->
      fuse_all_lt b r bound
    | _, Node Red c y d ->
      fuse_all_lt l c bound

let rec fuse_all_gt (l r: rbtree) (bound: int)
  : Lemma
    (requires all_gt l bound /\ all_gt r bound)
    (ensures all_gt (fuse l r) bound)
    (decreases (node_count l + node_count r))
  = match l, r with
    | Leaf, _ -> ()
    | _, Leaf -> ()
    | Node Red a x b, Node Red c y d ->
      fuse_all_gt b c bound
    | Node Black a x b, Node Black c y d ->
      fuse_all_gt b c bound;
      (match fuse b c with
       | Node Red _ _ _ -> ()
       | _ -> balL_all_gt a x (Node Black (fuse b c) y d) bound)
    | Node Red a x b, _ ->
      fuse_all_gt b r bound
    | _, Node Red c y d ->
      fuse_all_gt l c bound
#pop-options

// fuse preserves BST — uses explicit bounds (all_lt l sep, all_gt r sep)
#push-options "--fuel 5 --ifuel 3 --z3rlimit 80"
let rec fuse_is_bst (l r: rbtree) (sep: int)
  : Lemma
    (requires is_bst l /\ is_bst r /\ all_lt l sep /\ all_gt r sep)
    (ensures is_bst (fuse l r))
    (decreases (node_count l + node_count r))
  = match l, r with
    | Leaf, _ -> ()
    | _, Leaf -> ()
    | Node Red a x b, Node Red c y d ->
      // Derive cross-bounds: all_gt c x and all_lt b y
      all_gt_weaken c sep x;
      all_lt_weaken b sep y;
      fuse_is_bst b c sep;
      fuse_all_gt b c x;
      fuse_all_lt b c y;
      (match fuse b c with
       | Node Red b' z c' ->
         all_lt_weaken a x z;
         all_gt_weaken d y z
       | _ ->
         all_gt_weaken d y x)
    | Node Black a x b, Node Black c y d ->
      all_gt_weaken c sep x;
      all_lt_weaken b sep y;
      fuse_is_bst b c sep;
      fuse_all_gt b c x;
      fuse_all_lt b c y;
      (match fuse b c with
       | Node Red b' z c' ->
         all_lt_weaken a x z;
         all_gt_weaken d y z
       | _ ->
         all_gt_weaken d y x;
         balL_is_bst a x (Node Black (fuse b c) y d))
    | Node Red a x b, _ ->
      all_gt_weaken r sep x;
      fuse_is_bst b r sep;
      fuse_all_gt b r x
    | _, Node Red c y d ->
      all_lt_weaken l sep y;
      fuse_is_bst l c sep;
      fuse_all_lt l c y
#pop-options

// del preserves all_lt / all_gt
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec del_all_lt (t: rbtree) (k: int) (bound: int)
  : Lemma
    (requires is_bst t /\ all_lt t bound)
    (ensures all_lt (del t k) bound)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        del_all_lt l k bound;
        (match l with
         | Node Black _ _ _ -> balL_all_lt (del l k) v r bound
         | _ -> ())
      end else if k > v then begin
        del_all_lt r k bound;
        (match r with
         | Node Black _ _ _ -> balR_all_lt l v (del r k) bound
         | _ -> ())
      end else
        fuse_all_lt l r bound

let rec del_all_gt (t: rbtree) (k: int) (bound: int)
  : Lemma
    (requires is_bst t /\ all_gt t bound)
    (ensures all_gt (del t k) bound)
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        del_all_gt l k bound;
        (match l with
         | Node Black _ _ _ -> balL_all_gt (del l k) v r bound
         | _ -> ())
      end else if k > v then begin
        del_all_gt r k bound;
        (match r with
         | Node Black _ _ _ -> balR_all_gt l v (del r k) bound
         | _ -> ())
      end else
        fuse_all_gt l r bound
#pop-options

// del preserves BST
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec del_preserves_bst (t: rbtree) (k: int)
  : Lemma
    (requires is_bst t)
    (ensures is_bst (del t k))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        del_preserves_bst l k;
        del_all_lt l k v;
        (match l with
         | Node Black _ _ _ -> balL_is_bst (del l k) v r
         | _ -> ())
      end else if k > v then begin
        del_preserves_bst r k;
        del_all_gt r k v;
        (match r with
         | Node Black _ _ _ -> balR_is_bst l v (del r k)
         | _ -> ())
      end else begin
        fuse_is_bst l r v
      end
#pop-options

let delete_preserves_bst (t: rbtree) (k: int)
  : Lemma
    (requires is_bst t)
    (ensures is_bst (delete t k))
  = del_preserves_bst t k

(*** Delete Correctness — RB Invariant Preservation ***)

// The RB invariant preservation proof for delete requires careful tracking of
// color-dependent invariants through balL/balR/fuse/del. The internal invariant
// of del is: del on a Black Node produces (same_bh, almost_no_red_red, bh - 1),
// and del on a Red Node produces (same_bh, no_red_red, same bh).
// The stronger no_red_red for Red parents follows because Red nodes' children
// are always Black (by no_red_red), constraining which balL/balR cases fire.

// ====== Properties of balL (with weak left precondition) ======
// balL is called with del's output (which may only have almost_no_red_red)

#push-options "--fuel 5 --ifuel 3 --z3rlimit 80"
let balL_props (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires same_bh l /\ same_bh r /\ bh l + 1 = bh r /\
             almost_no_red_red l /\ no_red_red r)
    (ensures same_bh (balL l v r) /\
             bh (balL l v r) = bh r /\
             almost_no_red_red (balL l v r))
  = match l, r with
    | Node Red a x b, _ -> ()
    | _, Node Black b y c ->
      balance_same_bh Black l v (Node Red b y c);
      balance_bh Black l v (Node Red b y c);
      // l is not Red (case 1 didn't fire), so Leaf or Black => no_red_red l
      balance_restores_no_red_red_right Black l v (Node Red b y c)
    | _, Node Red (Node Black b y c) z d ->
      balance_same_bh Black c z (redden d);
      balance_bh Black c z (redden d);
      balance_restores_no_red_red_right Black c z (redden d)
    | _ -> ()
#pop-options

// Stronger: when r is Black or Leaf (sibling of a Red parent's child),
// balL always produces no_red_red (not just almost_no_red_red)
#push-options "--fuel 5 --ifuel 3 --z3rlimit 80"
let balL_strong (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires same_bh l /\ same_bh r /\ bh l + 1 = bh r /\
             almost_no_red_red l /\ no_red_red r /\
             (Leaf? r \/ Black? (Node?.c r)))
    (ensures same_bh (balL l v r) /\
             bh (balL l v r) = bh r /\
             no_red_red (balL l v r))
  = match l, r with
    | Node Red a x b, _ -> ()
    | _, Node Black b y c ->
      balance_same_bh Black l v (Node Red b y c);
      balance_bh Black l v (Node Red b y c);
      balance_restores_no_red_red_right Black l v (Node Red b y c)
    | _ -> () // r is Black or Leaf, so case 3 (r = Node Red ...) cannot fire
#pop-options

// ====== Properties of balR (symmetric) ======

#push-options "--fuel 5 --ifuel 3 --z3rlimit 80"
let balR_props (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires same_bh l /\ same_bh r /\ bh l = bh r + 1 /\
             no_red_red l /\ almost_no_red_red r)
    (ensures same_bh (balR l v r) /\
             bh (balR l v r) = bh l /\
             almost_no_red_red (balR l v r))
  = match l, r with
    | _, Node Red b y c -> ()
    | Node Black a x b, _ ->
      balance_same_bh Black (Node Red a x b) v r;
      balance_bh Black (Node Red a x b) v r;
      balance_restores_no_red_red_left Black (Node Red a x b) v r
    | Node Red a x (Node Black b y c), _ ->
      balance_same_bh Black (redden a) x b;
      balance_bh Black (redden a) x b;
      balance_restores_no_red_red_left Black (redden a) x b
    | _ -> ()
#pop-options

#push-options "--fuel 5 --ifuel 3 --z3rlimit 80"
let balR_strong (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires same_bh l /\ same_bh r /\ bh l = bh r + 1 /\
             no_red_red l /\ almost_no_red_red r /\
             (Leaf? l \/ Black? (Node?.c l)))
    (ensures same_bh (balR l v r) /\
             bh (balR l v r) = bh l /\
             no_red_red (balR l v r))
  = match l, r with
    | _, Node Red b y c -> ()
    | Node Black a x b, _ ->
      balance_same_bh Black (Node Red a x b) v r;
      balance_bh Black (Node Red a x b) v r;
      balance_restores_no_red_red_left Black (Node Red a x b) v r
    | _ -> ()
#pop-options

// ====== Properties of fuse ======

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec fuse_props (l r: rbtree)
  : Lemma
    (requires same_bh l /\ same_bh r /\ bh l = bh r /\ no_red_red l /\ no_red_red r)
    (ensures
      same_bh (fuse l r) /\
      bh (fuse l r) = bh l /\
      ((Leaf? l \/ Black? (Node?.c l)) /\ (Leaf? r \/ Black? (Node?.c r)) ==>
        no_red_red (fuse l r)) /\
      almost_no_red_red (fuse l r))
    (decreases (node_count l + node_count r))
  = match l, r with
    | Leaf, _ -> ()
    | _, Leaf -> ()
    | Node Red a x b, Node Red c y d ->
      fuse_props b c;
      (match fuse b c with
       | Node Red b' z c' -> ()
       | _ -> ())
    | Node Black a x b, Node Black c y d ->
      fuse_props b c;
      (match fuse b c with
       | Node Red b' z c' -> ()
       | _ ->
         balL_props a x (Node Black (fuse b c) y d))
    | Node Red a x b, _ ->
      fuse_props b r
    | _, Node Red c y d ->
      fuse_props l c
#pop-options

// ====== Properties of del ======
// del on a Black Node: bh decreases by 1, almost_no_red_red
// del on a Red Node: bh unchanged, no_red_red (stronger, since children Black)
// del on Leaf: identity

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec del_props (t: rbtree) (k: int)
  : Lemma
    (requires same_bh t /\ no_red_red t)
    (ensures
      same_bh (del t k) /\
      (Leaf? t ==> del t k == Leaf) /\
      (Node? t /\ Black? (Node?.c t) ==>
        bh (del t k) = bh t - 1 /\ almost_no_red_red (del t k)) /\
      (Node? t /\ Red? (Node?.c t) ==>
        bh (del t k) = bh t /\ no_red_red (del t k)))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        match l with
        | Node Black _ _ _ ->
          del_props l k;
          if c = Red then
            // Red parent: r is Black/Leaf (no_red_red), so balL_strong applies
            balL_strong (del l k) v r
          else
            balL_props (del l k) v r
        | _ ->
          // l is Leaf or Node Red: del l k has IH-dependent properties
          (match l with
           | Leaf -> ()
           | Node Red _ _ _ ->
             del_props l k)
      end else if k > v then begin
        match r with
        | Node Black _ _ _ ->
          del_props r k;
          if c = Red then
            balR_strong l v (del r k)
          else
            balR_props l v (del r k)
        | _ ->
          (match r with
           | Leaf -> ()
           | Node Red _ _ _ ->
             del_props r k)
      end else
        fuse_props l r
#pop-options

// delete maintains all RB properties
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let delete_is_rbtree (t: rbtree) (k: int)
  : Lemma
    (requires is_rbtree t /\ is_bst t)
    (ensures is_rbtree (delete t k) /\ is_bst (delete t k))
  = del_props t k;
    del_preserves_bst t k
#pop-options

(*** Insert Preserves Node Count ***)

// balance preserves node count
#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let balance_node_count (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma (ensures node_count (balance c l v r) = 1 + node_count l + node_count r)
  = ()
#pop-options

// ins increases node count by 0 (if key exists) or 1 (if key is new)
#push-options "--fuel 3 --ifuel 1 --z3rlimit 30"
let rec ins_node_count (t: rbtree) (k: int)
  : Lemma
    (requires is_bst t)
    (ensures node_count (ins t k) = (if mem k t then node_count t else node_count t + 1))
    (decreases t)
  = match t with
    | Leaf -> ()
    | Node c l v r ->
      if k < v then begin
        ins_node_count l k;
        balance_node_count c (ins l k) v r;
        bst_lt_not_mem r v k
      end else if k > v then begin
        ins_node_count r k;
        balance_node_count c l v (ins r k);
        bst_gt_not_mem l v k
      end else ()
#pop-options

// insert increases node count by 0 or 1
let insert_node_count (t: rbtree) (k: int)
  : Lemma
    (requires is_bst t)
    (ensures node_count (insert t k) = (if mem k t then node_count t else node_count t + 1))
  = ins_node_count t k
