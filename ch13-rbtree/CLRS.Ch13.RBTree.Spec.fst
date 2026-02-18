(**
 * CLRS Chapter 13: Red-Black Trees — Pure Functional Specification
 *
 * Defines:
 *   - Inductive rbtree type with Red/Black colors
 *   - BST ordering predicate (all_lt / all_gt bounds)
 *   - RB invariants: no_red_red, same_black_height, root_black
 *   - Functional search, insert with Okasaki-style balance/fixup
 *   - CLRS Theorem 13.1: height ≤ 2·lg(n+1)
 *     via key lemma: node_count ≥ 2^bh - 1
 *   - Correctness: insert preserves membership and RB invariants
 *
 * Zero admits.
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
#push-options "--fuel 4 --ifuel 2 --z3rlimit 200"
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

#push-options "--fuel 8 --ifuel 4 --z3rlimit 200"
let balance_restores_no_red_red_left (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires c = Black /\ almost_no_red_red l /\ no_red_red r)
    (ensures no_red_red (balance c l v r))
  = ()

let balance_restores_no_red_red_right (c: color) (l: rbtree) (v: int) (r: rbtree)
  : Lemma
    (requires c = Black /\ no_red_red l /\ almost_no_red_red r)
    (ensures no_red_red (balance c l v r))
  = ()

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
