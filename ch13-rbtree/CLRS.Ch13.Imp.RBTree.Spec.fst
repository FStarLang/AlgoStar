(*
   Red-Black Tree — CLRS-faithful pure functional specification

   CLRS Chapter 13: Red-Black Trees with parent pointers.
   Models the CLRS pseudocode exactly:
   - LEFT-ROTATE, RIGHT-ROTATE (§13.2)
   - RB-INSERT with RB-INSERT-FIXUP (§13.3)
   - RB-DELETE with RB-TRANSPLANT and RB-DELETE-FIXUP (§13.4)
   - TREE-MINIMUM, TREE-SEARCH, TREE-SUCCESSOR (§12.2)

   Nodes are identified by integer IDs. A node store maps IDs to node records.
   The sentinel is node 0 (always Black). Internal nodes have IDs >= 1.

   This spec uses a functional "store" model: operations return an updated store.
   Each node has { key, color, left, right, p } fields.

   Iterative CLRS loops are modeled as recursive functions with a fuel parameter.
   The fuel corresponds to the tree height and is always sufficient for correct trees.
*)
module CLRS.Ch13.Imp.RBTree.Spec

open FStar.Map
open FStar.List.Tot

// ========== Colors ==========

type color = | Red | Black

// ========== Node representation ==========

// Nodes are identified by integer IDs.
// ID 0 is the sentinel (T.nil): always Black, no meaningful key.
type node_id = nat

let nil_id : node_id = 0

type rb_node = {
  key:   int;
  color: color;
  left:  node_id;
  right: node_id;
  p:     node_id;  // parent
}

// The sentinel node
let nil_node : rb_node = {
  key = 0;
  color = Black;
  left = nil_id;
  right = nil_id;
  p = nil_id;
}

// ========== Store: map from node_id to rb_node ==========

type store = Map.t node_id rb_node

let empty_store : store = Map.const nil_node

let get (s: store) (n: node_id) : rb_node = Map.sel s n

let set (s: store) (n: node_id) (v: rb_node) : store = Map.upd s n v

// ========== Tree: root + store ==========

noeq
type rb_tree = {
  root: node_id;
  s:    store;
}

let empty_tree : rb_tree = {
  root = nil_id;
  s = empty_store;
}

// ========== Node accessors ==========

let key_of (t: rb_tree) (x: node_id) : int = (get t.s x).key
let color_of (t: rb_tree) (x: node_id) : color = (get t.s x).color
let left_of (t: rb_tree) (x: node_id) : node_id = (get t.s x).left
let right_of (t: rb_tree) (x: node_id) : node_id = (get t.s x).right
let parent_of (t: rb_tree) (x: node_id) : node_id = (get t.s x).p

let is_nil (x: node_id) : bool = x = nil_id

// ========== LEFT-ROTATE (§13.2) ==========
// Assumes x.right != nil_id

let left_rotate (t: rb_tree) (x: node_id) : rb_tree =
  let s0 = t.s in
  let xn = get s0 x in
  let y = xn.right in
  let yn = get s0 y in
  // Step 1: x.right = y.left
  let s1 = set s0 x { xn with right = yn.left } in
  // Step 2: if y.left != nil then y.left.p = x
  let s2 = if yn.left <> nil_id
            then set s1 yn.left { get s1 yn.left with p = x }
            else s1 in
  // Step 3: y.p = x.p
  let s3 = set s2 y { get s2 y with p = xn.p } in
  // Step 4: link x's parent to y
  let root' =
    if xn.p = nil_id then y
    else t.root in
  let s4 = if xn.p <> nil_id then
              let pn = get s3 xn.p in
              if pn.left = x
              then set s3 xn.p { pn with left = y }
              else set s3 xn.p { pn with right = y }
            else s3 in
  // Step 5: y.left = x
  let s5 = set s4 y { get s4 y with left = x } in
  // Step 6: x.p = y
  let s6 = set s5 x { get s5 x with p = y } in
  { root = root'; s = s6 }

// ========== RIGHT-ROTATE (symmetric) ==========

let right_rotate (t: rb_tree) (y: node_id) : rb_tree =
  let s0 = t.s in
  let yn = get s0 y in
  let x = yn.left in
  let xn = get s0 x in
  let s1 = set s0 y { yn with left = xn.right } in
  let s2 = if xn.right <> nil_id
            then set s1 xn.right { get s1 xn.right with p = y }
            else s1 in
  let s3 = set s2 x { get s2 x with p = yn.p } in
  let root' =
    if yn.p = nil_id then x
    else t.root in
  let s4 = if yn.p <> nil_id then
              let pn = get s3 yn.p in
              if pn.left = y
              then set s3 yn.p { pn with left = x }
              else set s3 yn.p { pn with right = x }
            else s3 in
  let s5 = set s4 x { get s4 x with right = y } in
  let s6 = set s5 y { get s5 y with p = x } in
  { root = root'; s = s6 }

// ========== TREE-MINIMUM (§12.2) ==========

let rec tree_minimum (s: store) (x: node_id) (fuel: nat) : Tot node_id (decreases fuel) =
  if fuel = 0 then x
  else if (get s x).left = nil_id then x
  else tree_minimum s (get s x).left (fuel - 1)

// ========== TREE-MAXIMUM (§12.2) ==========

let rec tree_maximum (s: store) (x: node_id) (fuel: nat) : Tot node_id (decreases fuel) =
  if fuel = 0 then x
  else if (get s x).right = nil_id then x
  else tree_maximum s (get s x).right (fuel - 1)

// ========== TREE-SEARCH (§12.2) ==========

let rec tree_search (s: store) (x: node_id) (k: int) (fuel: nat) : Tot node_id (decreases fuel) =
  if fuel = 0 then x
  else if x = nil_id then nil_id
  else
    let xn = get s x in
    if k = xn.key then x
    else if k < xn.key
    then tree_search s xn.left k (fuel - 1)
    else tree_search s xn.right k (fuel - 1)

// ========== TREE-SUCCESSOR (§12.2) ==========

let rec walk_up_right (s: store) (x: node_id) (y: node_id) (fuel: nat) : Tot node_id (decreases fuel) =
  if fuel = 0 then y
  else if y = nil_id then nil_id
  else if x = (get s y).right
  then walk_up_right s y (get s y).p (fuel - 1)
  else y

let tree_successor (s: store) (x: node_id) (fuel: nat) : node_id =
  let xn = get s x in
  if xn.right <> nil_id then
    tree_minimum s xn.right fuel
  else
    walk_up_right s x xn.p fuel

// ========== TREE-PREDECESSOR (§12.2) ==========

let rec walk_up_left (s: store) (x: node_id) (y: node_id) (fuel: nat) : Tot node_id (decreases fuel) =
  if fuel = 0 then y
  else if y = nil_id then nil_id
  else if x = (get s y).left
  then walk_up_left s y (get s y).p (fuel - 1)
  else y

let tree_predecessor (s: store) (x: node_id) (fuel: nat) : node_id =
  let xn = get s x in
  if xn.left <> nil_id then
    tree_maximum s xn.left fuel
  else
    walk_up_left s x xn.p fuel

// ========== RB-INSERT-FIXUP (§13.3) ==========

let rec rb_insert_fixup (t: rb_tree) (z: node_id) (fuel: nat) : Tot rb_tree (decreases fuel) =
  if fuel = 0 then t
  else
  let s = t.s in
  let zn = get s z in
  let pn = get s zn.p in
  if pn.color <> Red then
    // z.p is black -> done. Ensure root is black.
    { t with s = set t.s t.root { get t.s t.root with color = Black } }
  else
  let pp = pn.p in
  let ppn = get s pp in
  if zn.p = ppn.left then begin
    // z.p is left child of grandparent
    let y = ppn.right in   // uncle
    let yn = get s y in
    if yn.color = Red then begin
      // Case 1: uncle is red — recolor and move up
      let s = set s zn.p { pn with color = Black } in
      let s = set s y { yn with color = Black } in
      let s = set s pp { get s pp with color = Red } in
      rb_insert_fixup { t with s = s } pp (fuel - 1)
    end
    else begin
      // Case 2: z is right child -> left rotate to make it case 3
      let t, z =
        if z = (get t.s zn.p).right then
          let t' = left_rotate t zn.p in
          (t', zn.p)
        else (t, z)
      in
      // Case 3: z is left child -> recolor + right rotate
      let s = t.s in
      let zn' = get s z in
      let s = set s zn'.p { get s zn'.p with color = Black } in
      let pp' = (get s zn'.p).p in
      let s = set s pp' { get s pp' with color = Red } in
      let t = right_rotate { t with s = s } pp' in
      { t with s = set t.s t.root { get t.s t.root with color = Black } }
    end
  end
  else begin
    // Symmetric: z.p is right child of grandparent
    let y = ppn.left in
    let yn = get s y in
    if yn.color = Red then begin
      let s = set s zn.p { pn with color = Black } in
      let s = set s y { yn with color = Black } in
      let s = set s pp { get s pp with color = Red } in
      rb_insert_fixup { t with s = s } pp (fuel - 1)
    end
    else begin
      let t, z =
        if z = (get t.s zn.p).left then
          let t' = right_rotate t zn.p in
          (t', zn.p)
        else (t, z)
      in
      let s = t.s in
      let zn' = get s z in
      let s = set s zn'.p { get s zn'.p with color = Black } in
      let pp' = (get s zn'.p).p in
      let s = set s pp' { get s pp' with color = Red } in
      let t = left_rotate { t with s = s } pp' in
      { t with s = set t.s t.root { get t.s t.root with color = Black } }
    end
  end

// ========== RB-INSERT (§13.3) ==========

let rec find_parent (s: store) (x: node_id) (y: node_id) (k: int) (fuel: nat) : Tot node_id (decreases fuel) =
  if fuel = 0 then y
  else if x = nil_id then y
  else
    let xn = get s x in
    if k < xn.key
    then find_parent s xn.left x k (fuel - 1)
    else find_parent s xn.right x k (fuel - 1)

let rb_insert (t: rb_tree) (z: node_id) (k: int) (fuel: nat) : rb_tree =
  let y = find_parent t.s t.root nil_id k fuel in
  let zn = { key = k; color = Red; left = nil_id; right = nil_id; p = y } in
  let s = set t.s z zn in
  let root =
    if y = nil_id then z
    else t.root in
  let s =
    if y <> nil_id then
      let yn = get s y in
      if k < yn.key
      then set s y { yn with left = z }
      else set s y { yn with right = z }
    else s in
  rb_insert_fixup { root = root; s = s } z fuel

// ========== RB-TRANSPLANT (§13.4) ==========

let rb_transplant (t: rb_tree) (u: node_id) (v: node_id) : rb_tree =
  let s = t.s in
  let un = get s u in
  let root =
    if un.p = nil_id then v
    else t.root in
  let s =
    if un.p <> nil_id then
      let pn = get s un.p in
      if pn.left = u
      then set s un.p { pn with left = v }
      else set s un.p { pn with right = v }
    else s in
  let s = set s v { get s v with p = un.p } in
  { root = root; s = s }

// ========== RB-DELETE-FIXUP (§13.4) ==========

let rec rb_delete_fixup (t: rb_tree) (x: node_id) (fuel: nat) : Tot rb_tree (decreases fuel) =
  if fuel = 0 then t
  else
  if x = t.root || (get t.s x).color = Red then
    { t with s = set t.s x { get t.s x with color = Black } }
  else
  let s = t.s in
  let xn = get s x in
  let pn = get s xn.p in
  if x = pn.left then begin
    // x is left child
    let w = pn.right in
    let wn = get s w in
    // Case 1: sibling w is red
    let t, s, w =
      if wn.color = Red then begin
        let s = set s w { wn with color = Black } in
        let s = set s xn.p { get s xn.p with color = Red } in
        let t' = left_rotate { t with s = s } xn.p in
        let w' = (get t'.s xn.p).right in
        (t', t'.s, w')
      end
      else (t, s, w)
    in
    let wn = get s w in
    if (get s wn.left).color = Black && (get s wn.right).color = Black then begin
      // Case 2: both children of w are black
      let s = set s w { wn with color = Red } in
      rb_delete_fixup { t with s = s } xn.p (fuel - 1)
    end
    else begin
      // Case 3: w's right child is black -> right rotate w
      let t, s, w =
        if (get s wn.right).color = Black then begin
          let s = set s wn.left { get s wn.left with color = Black } in
          let s = set s w { get s w with color = Red } in
          let t' = right_rotate { t with s = s } w in
          let w' = (get t'.s xn.p).right in
          (t', t'.s, w')
        end
        else (t, s, w)
      in
      // Case 4: w's right child is red
      let wn = get s w in
      let s = set s w { wn with color = (get s xn.p).color } in
      let s = set s xn.p { get s xn.p with color = Black } in
      let s = set s wn.right { get s wn.right with color = Black } in
      let t = left_rotate { t with s = s } xn.p in
      { t with s = set t.s t.root { get t.s t.root with color = Black } }
    end
  end
  else begin
    // Symmetric: x is right child
    let w = pn.left in
    let wn = get s w in
    let t, s, w =
      if wn.color = Red then begin
        let s = set s w { wn with color = Black } in
        let s = set s xn.p { get s xn.p with color = Red } in
        let t' = right_rotate { t with s = s } xn.p in
        let w' = (get t'.s xn.p).left in
        (t', t'.s, w')
      end
      else (t, s, w)
    in
    let wn = get s w in
    if (get s wn.right).color = Black && (get s wn.left).color = Black then begin
      let s = set s w { wn with color = Red } in
      rb_delete_fixup { t with s = s } xn.p (fuel - 1)
    end
    else begin
      let t, s, w =
        if (get s wn.left).color = Black then begin
          let s = set s wn.right { get s wn.right with color = Black } in
          let s = set s w { get s w with color = Red } in
          let t' = left_rotate { t with s = s } w in
          let w' = (get t'.s xn.p).left in
          (t', t'.s, w')
        end
        else (t, s, w)
      in
      let wn = get s w in
      let s = set s w { wn with color = (get s xn.p).color } in
      let s = set s xn.p { get s xn.p with color = Black } in
      let s = set s wn.left { get s wn.left with color = Black } in
      let t = right_rotate { t with s = s } xn.p in
      { t with s = set t.s t.root { get t.s t.root with color = Black } }
    end
  end

// ========== RB-DELETE (§13.4) ==========

let rb_delete (t: rb_tree) (z: node_id) (fuel: nat) : rb_tree =
  let s = t.s in
  let zn = get s z in
  if zn.left = nil_id then begin
    // No left child
    let x = zn.right in
    let t = rb_transplant t z zn.right in
    if zn.color = Black
    then rb_delete_fixup t x fuel
    else t
  end
  else if zn.right = nil_id then begin
    // No right child
    let x = zn.left in
    let t = rb_transplant t z zn.left in
    if zn.color = Black
    then rb_delete_fixup t x fuel
    else t
  end
  else begin
    // Two children: find successor
    let y = tree_minimum s zn.right fuel in
    let yn = get s y in
    let y_orig_color = yn.color in
    let x = yn.right in
    let t =
      if yn.p = z then
        { t with s = set t.s x { get t.s x with p = y } }
      else begin
        let t = rb_transplant t y yn.right in
        let s = t.s in
        let s = set s y { get s y with right = zn.right } in
        let s = set s zn.right { get s zn.right with p = y } in
        { t with s = s }
      end
    in
    let t = rb_transplant t z y in
    let s = t.s in
    let s = set s y { get s y with left = zn.left } in
    let s = set s zn.left { get s zn.left with p = y } in
    let s = set s y { get s y with color = zn.color } in
    let t = { t with s = s } in
    if y_orig_color = Black
    then rb_delete_fixup t x fuel
    else t
  end

// ========== Membership (set-theoretic view) ==========

let rec mem (s: store) (x: node_id) (k: int) (fuel: nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else if x = nil_id then false
  else
    let xn = get s x in
    k = xn.key || mem s xn.left k (fuel - 1) || mem s xn.right k (fuel - 1)

// ========== Inorder traversal ==========

let rec inorder (s: store) (x: node_id) (fuel: nat) : Tot (list int) (decreases fuel) =
  if fuel = 0 then []
  else if x = nil_id then []
  else
    let xn = get s x in
    inorder s xn.left (fuel - 1) @ [xn.key] @ inorder s xn.right (fuel - 1)
