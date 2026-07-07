module CLRS.Ch10.DoublyLinkedList.Rubric
#lang-pulse

open Pulse.Lib.Pervasives

module BC = CLRS.Common.Complexity.Box.Class
module LLC = CLRS.Common.Complexity.LinkedList.Class
module L = FStar.List.Tot
module MR = Pulse.Lib.MonotonicGhostRef

noeq
type node
  (box:([@@@strictly_positive] _:Type0 -> Type0))
  (a:Type0)
= {
  key: a;
  prev: option (box (node box a));
  next: option (box (node box a));
}

let dptr
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    (a:Type0)
  : Type0
  = option (box (node box a))

noeq
type dll
  (box:([@@@strictly_positive] _:Type0 -> Type0))
  (a:Type0)
= {
  head: dptr box a;
  tail: dptr box a;
}

let nil (#box:([@@@strictly_positive] _:Type0 -> Type0)) (#a:Type0) : dll box a =
  { head = None; tail = None }

let node_owns
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (p:box (node box a))
    (pr:dptr box a)
    (k:a)
    (n:dptr box a)
  : slprop
  = bc.BC.pts_to p (hide { key = k; prev = pr; next = n })

let rec chain
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (h:dptr box a)
    (prev:dptr box a)
    (l:list a)
    (tail:dptr box a)
  : Tot slprop (decreases L.length l)
  = match l with
    | [] -> pure (h == None /\ tail == prev)
    | hd :: tl ->
      exists* (p:box (node box a)) (nxt:dptr box a).
        pure (h == Some p) **
        node_owns #ctr #box p prev hd nxt **
        chain #ctr #box nxt (Some p) tl tail

let owns
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (xs:dll box a)
    (l:list a)
  : Tot slprop
  = chain #ctr #box xs.head None l xs.tail

let snoc_cons_eq (#a:Type0) (x:a) (pre:list a) (last:a)
  : Lemma (x :: LLC.snoc pre last == LLC.snoc (x :: pre) last)
= ()

let rec prefix
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (h:dptr box a)
    (prev:dptr box a)
    (pre:list a)
    (tail_prev:dptr box a)
    (tail:box (node box a))
  : Tot slprop (decreases L.length pre)
  = match pre with
    | [] -> pure (h == Some tail /\ tail_prev == prev)
    | hd :: tl ->
      exists* (p:box (node box a)) (nxt:dptr box a).
        pure (h == Some p) **
        node_owns #ctr #box p prev hd nxt **
        prefix #ctr #box nxt (Some p) tl tail_prev tail

ghost
fn chain_none_nil
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (prev:dptr box a)
    (tail:dptr box a)
    (#l:erased (list a))
  preserves chain #ctr #box None prev l tail
  ensures pure (l == [] /\ tail == prev)
{
  let ll = reveal l;
  match ll {
    [] -> {
      rewrite each l as ([] #a) in (chain #ctr #box None prev l tail);
      unfold (chain #ctr #box None prev ([] #a) tail);
      fold (chain #ctr #box None prev ([] #a) tail);
      rewrite (chain #ctr #box None prev ([] #a) tail)
        as (chain #ctr #box None prev l tail)
    }
    hd :: tl -> {
      rewrite each l as (hd :: tl) in (chain #ctr #box None prev l tail);
      unfold (chain #ctr #box None prev (hd :: tl) tail);
      unreachable ()
    }
  }
}

ghost
fn chain_some_cons
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (p:box (node box a))
    (prev:dptr box a)
    (tail:dptr box a)
    (#l:erased (list a))
  preserves chain #ctr #box (Some p) prev l tail
  ensures pure (Cons? l)
{
  let ll = reveal l;
  match ll {
    [] -> {
      rewrite each l as ([] #a) in (chain #ctr #box (Some p) prev l tail);
      unfold (chain #ctr #box (Some p) prev ([] #a) tail);
      unreachable ()
    }
    hd :: tl -> { () }
  }
}

fn set_first_prev
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (p:box (node box a))
    (old_prev new_prev:dptr box a)
    (#l:erased (list a))
    (tail:dptr box a)
    (#i:erased nat)
  requires chain #ctr #box (Some p) old_prev l tail **
           MR.pts_to ctr #1.0R i **
           pure (Cons? l)
  ensures chain #ctr #box (Some p) new_prev l tail **
          MR.pts_to ctr #1.0R (i + BC.read_cost + BC.write_cost)
{
  rewrite each l as (L.hd l :: L.tl l) in (chain #ctr #box (Some p) old_prev l tail);
  unfold (chain #ctr #box (Some p) old_prev (L.hd l :: L.tl l) tail);
  with p0 nxt. _;
  rewrite each p0 as p;
  unfold (node_owns #ctr #box p old_prev (L.hd l) nxt);
  let nd = BC.read #ctr #box p;
  assert (pure (nd.key == L.hd l));
  assert (pure (nd.prev == old_prev));
  assert (pure (nd.next == nxt));
  BC.write #ctr #box p { nd with prev = new_prev };
  rewrite (bc.BC.pts_to p (hide { nd with prev = new_prev }))
    as (bc.BC.pts_to p (hide { key = L.hd l; prev = new_prev; next = nxt }));
  fold (node_owns #ctr #box p new_prev (L.hd l) nxt);
  fold (chain #ctr #box (Some p) new_prev (L.hd l :: L.tl l) tail);
  rewrite (chain #ctr #box (Some p) new_prev (L.hd l :: L.tl l) tail)
    as (chain #ctr #box (Some p) new_prev l tail)
}

ghost
fn chain_tail_some_cons_none
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (h:dptr box a)
    (tail:box (node box a))
    (#l:erased (list a))
  preserves chain #ctr #box h None l (Some tail)
  ensures pure (Cons? l)
{
  let ll = reveal l;
  match ll {
    [] -> {
      rewrite each l as ([] #a) in (chain #ctr #box h None l (Some tail));
      unfold (chain #ctr #box h None ([] #a) (Some tail));
      unreachable ()
    }
    hd :: tl -> { () }
  }
}

ghost
fn rec chain_tail_none_prev_some_absurd
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (h:dptr box a)
    (p:box (node box a))
    (#l:erased (list a))
  requires chain #ctr #box h (Some p) l None
  ensures pure False
  decreases L.length (reveal l)
{
  let ll = reveal l;
  match ll {
    [] -> {
      rewrite each l as ([] #a) in (chain #ctr #box h (Some p) l None);
      unfold (chain #ctr #box h (Some p) ([] #a) None);
      unreachable ()
    }
    hd :: tl -> {
      rewrite each l as (hd :: tl) in (chain #ctr #box h (Some p) l None);
      unfold (chain #ctr #box h (Some p) (hd :: tl) None);
      with q nxt. _;
      chain_tail_none_prev_some_absurd #ctr #box #bc #a nxt q #tl;
      unreachable ()
    }
  }
}

ghost
fn chain_tail_none_nil
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (h:dptr box a)
    (#l:erased (list a))
  preserves chain #ctr #box h None l None
  ensures pure (l == [] /\ h == None)
{
  let ll = reveal l;
  match ll {
    [] -> {
      rewrite each l as ([] #a) in (chain #ctr #box h None l None);
      unfold (chain #ctr #box h None ([] #a) None);
      fold (chain #ctr #box h None ([] #a) None);
      rewrite (chain #ctr #box h None ([] #a) None)
        as (chain #ctr #box h None l None)
    }
    hd :: tl -> {
      rewrite each l as (hd :: tl) in (chain #ctr #box h None l None);
      unfold (chain #ctr #box h None (hd :: tl) None);
      with p nxt. _;
      chain_tail_none_prev_some_absurd #ctr #box #bc #a nxt p #tl;
      unreachable ()
    }
  }
}

ghost
fn rec split_last
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (h:dptr box a)
    (prev:dptr box a)
    (#l:erased (list a))
    (tail:box (node box a))
  requires chain #ctr #box h prev l (Some tail) ** pure (Cons? l)
  ensures exists* (pre:list a) (last:a).
    exists* (tail_prev:dptr box a).
    pure (l == LLC.snoc pre last) **
    prefix #ctr #box h prev pre tail_prev tail **
    node_owns #ctr #box tail tail_prev last None
  decreases L.length (reveal l)
{
  let ll = reveal l;
  match ll {
    [] -> {
      rewrite each l as ([] #a) in (chain #ctr #box h prev l (Some tail));
      unfold (chain #ctr #box h prev ([] #a) (Some tail));
      unreachable ()
    }
    hd :: tl -> {
      rewrite each l as (hd :: tl) in (chain #ctr #box h prev l (Some tail));
      unfold (chain #ctr #box h prev (hd :: tl) (Some tail));
      with p nxt. _;
      match tl {
        [] -> {
          unfold (chain #ctr #box nxt (Some p) ([] #a) (Some tail));
          rewrite each p as tail;
          rewrite each nxt as (None #(box (node box a)));
          fold (prefix #ctr #box h prev ([] #a) prev tail)
        }
        hd2 :: tl2 -> {
          split_last #ctr #box #bc #a nxt (Some p) #(hd2 :: tl2) tail;
          with pre last tail_prev. _;
          fold (prefix #ctr #box h prev (hd :: pre) tail_prev tail);
          snoc_cons_eq hd pre last
        }
      }
    }
  }
}

ghost
fn rec prefix_snoc
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (h:dptr box a)
    (prev:dptr box a)
    (#pre:erased (list a))
    (old_tail:box (node box a))
    (old_tail_prev:dptr box a)
    (last:a)
    (new_tail:box (node box a))
  requires
    prefix #ctr #box h prev pre old_tail_prev old_tail **
    node_owns #ctr #box old_tail old_tail_prev last (Some new_tail)
  ensures
    prefix #ctr #box h prev (LLC.snoc pre last) (Some old_tail) new_tail
  decreases L.length (reveal pre)
{
  let pp = reveal pre;
  match pp {
    [] -> {
      rewrite each pre as ([] #a) in (prefix #ctr #box h prev pre old_tail_prev old_tail);
      unfold (prefix #ctr #box h prev ([] #a) old_tail_prev old_tail);
      rewrite (node_owns #ctr #box old_tail old_tail_prev last (Some new_tail))
        as (node_owns #ctr #box old_tail prev last (Some new_tail));
      fold (prefix #ctr #box (Some new_tail) (Some old_tail) ([] #a) (Some old_tail) new_tail);
      fold (prefix #ctr #box h prev [last] (Some old_tail) new_tail);
      rewrite (prefix #ctr #box h prev [last] (Some old_tail) new_tail)
        as (prefix #ctr #box h prev (LLC.snoc pre last) (Some old_tail) new_tail)
    }
    hd :: tl -> {
      rewrite each pre as (hd :: tl) in (prefix #ctr #box h prev pre old_tail_prev old_tail);
      unfold (prefix #ctr #box h prev (hd :: tl) old_tail_prev old_tail);
      with p nxt. _;
      prefix_snoc #ctr #box #bc #a nxt (Some p) #tl old_tail old_tail_prev last new_tail;
      fold (prefix #ctr #box h prev (hd :: LLC.snoc tl last) (Some old_tail) new_tail);
      rewrite (prefix #ctr #box h prev (hd :: LLC.snoc tl last) (Some old_tail) new_tail)
        as (prefix #ctr #box h prev (LLC.snoc pre last) (Some old_tail) new_tail)
    }
  }
}

ghost
fn rec close_last
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (h:dptr box a)
    (prev:dptr box a)
    (#pre:erased (list a))
    (tail_prev:dptr box a)
    (tail:box (node box a))
    (last:a)
  requires
    prefix #ctr #box h prev pre tail_prev tail **
    node_owns #ctr #box tail tail_prev last None
  ensures
    chain #ctr #box h prev (LLC.snoc pre last) (Some tail)
  decreases L.length (reveal pre)
{
  let pp = reveal pre;
  match pp {
    [] -> {
      rewrite each pre as ([] #a) in (prefix #ctr #box h prev pre tail_prev tail);
      unfold (prefix #ctr #box h prev ([] #a) tail_prev tail);
      rewrite (node_owns #ctr #box tail tail_prev last None)
        as (node_owns #ctr #box tail prev last None);
      fold (chain #ctr #box None (Some tail) ([] #a) (Some tail));
      fold (chain #ctr #box h prev [last] (Some tail));
      rewrite (chain #ctr #box h prev [last] (Some tail))
        as (chain #ctr #box h prev (LLC.snoc pre last) (Some tail))
    }
    hd :: tl -> {
      rewrite each pre as (hd :: tl) in (prefix #ctr #box h prev pre tail_prev tail);
      unfold (prefix #ctr #box h prev (hd :: tl) tail_prev tail);
      with p nxt. _;
      close_last #ctr #box #bc #a nxt (Some p) #tl tail_prev tail last;
      fold (chain #ctr #box h prev (hd :: LLC.snoc tl last) (Some tail));
      rewrite (chain #ctr #box h prev (hd :: LLC.snoc tl last) (Some tail))
        as (chain #ctr #box h prev (LLC.snoc pre last) (Some tail))
    }
  }
}

let insert_head_bound (_n:nat) : nat = BC.alloc_cost + BC.read_cost + BC.write_cost
let append_tail_bound (_n:nat) : nat = BC.read_cost + BC.write_cost + BC.alloc_cost
let search_bound (n:nat) : nat = n
let delete_first_bound (n:nat) : nat = 4 * n + 2 * BC.free_cost
let delete_last_bound (n:nat) : nat = 4 * n + 2 * BC.free_cost

let remove_last_cons_tail_hit (#a:Type0) (same:a -> a -> Tot bool) (x hd:a) (tl:list a)
  : Lemma
      (requires LLC.mem_by same x tl == true)
      (ensures LLC.remove_last_by same x (hd :: tl) == hd :: LLC.remove_last_by same x tl)
= ()

let remove_last_cons_head_hit (#a:Type0) (same:a -> a -> Tot bool) (x hd:a) (tl:list a)
  : Lemma
      (requires LLC.mem_by same x tl == false /\ same x hd == true)
      (ensures LLC.remove_last_by same x (hd :: tl) == tl)
= ()

let remove_last_cons_miss (#a:Type0) (same:a -> a -> Tot bool) (x hd:a) (tl:list a)
  : Lemma
      (requires LLC.mem_by same x tl == false /\ same x hd == false)
      (ensures LLC.remove_last_by same x (hd :: tl) == hd :: tl)
= ()

let rec remove_last_no_mem (#a:Type0) (same:a -> a -> Tot bool) (x:a) (l:list a)
  : Lemma
      (requires LLC.mem_by same x l == false)
      (ensures LLC.remove_last_by same x l == l)
      (decreases l)
= match l with
  | [] -> ()
  | hd :: tl -> remove_last_no_mem same x tl

fn insert_head
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (xs:dll box a)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires owns #ctr #box xs l ** MR.pts_to ctr #1.0R i
  returns xs':dll box a
  ensures exists* ticks.
    owns #ctr #box xs' (x :: l) **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks <= i + insert_head_bound (L.length l))
{
  rewrite (owns #ctr #box xs l) as (chain #ctr #box xs.head None l xs.tail);
  match xs.head {
    None -> {
      chain_none_nil #ctr #box #bc #a None xs.tail #l;
      unfold (chain #ctr #box None None l xs.tail);
      rewrite each l as ([] #a);
      let p = BC.alloc #ctr #box {
        key = x;
        prev = (None #(box (node box a)));
        next = (None #(box (node box a)))
      };
      fold (node_owns #ctr #box p None x None);
      fold (chain #ctr #box None (Some p) ([] #a) (Some p));
      fold (chain #ctr #box (Some p) None [x] (Some p));
      rewrite (chain #ctr #box (Some p) None [x] (Some p))
        as (owns #ctr #box { head = Some p; tail = Some p } (x :: l));
      { head = Some p; tail = Some p }
    }
    Some old -> {
      chain_some_cons #ctr #box #bc #a old None xs.tail #l;
      let p = BC.alloc #ctr #box {
        key = x;
        prev = (None #(box (node box a)));
        next = Some old
      };
      set_first_prev #ctr #box #bc #a old None (Some p) #l xs.tail;
      fold (node_owns #ctr #box p None x (Some old));
      fold (chain #ctr #box (Some p) None (x :: l) xs.tail);
      rewrite (chain #ctr #box (Some p) None (x :: l) xs.tail)
        as (owns #ctr #box { head = Some p; tail = xs.tail } (x :: l));
      { head = Some p; tail = xs.tail }
    }
  }
}

fn append_tail
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (xs:dll box a)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires owns #ctr #box xs l ** MR.pts_to ctr #1.0R i
  returns xs':dll box a
  ensures exists* ticks.
    owns #ctr #box xs' (LLC.snoc l x) **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks <= i + append_tail_bound (L.length l))
{
  rewrite (owns #ctr #box xs l) as (chain #ctr #box xs.head None l xs.tail);
  match xs.tail {
    None -> {
      chain_tail_none_nil #ctr #box #bc #a xs.head #l;
      unfold (chain #ctr #box xs.head None l None);
      rewrite each l as ([] #a);
      let p = BC.alloc #ctr #box {
        key = x;
        prev = (None #(box (node box a)));
        next = (None #(box (node box a)))
      };
      fold (node_owns #ctr #box p None x None);
      fold (chain #ctr #box None (Some p) ([] #a) (Some p));
      fold (chain #ctr #box (Some p) None [x] (Some p));
      rewrite (chain #ctr #box (Some p) None [x] (Some p))
        as (owns #ctr #box { head = Some p; tail = Some p } (LLC.snoc l x));
      { head = Some p; tail = Some p }
    }
    Some t -> {
      chain_tail_some_cons_none #ctr #box #bc #a xs.head t #l;
      split_last #ctr #box #bc #a xs.head None #l t;
      with pre last tail_prev. _;
      unfold (node_owns #ctr #box t tail_prev last None);
      let nd = BC.read #ctr #box t;
      assert (pure (nd.key == last));
      assert (pure (nd.prev == tail_prev));
      assert (pure (nd.next == None));
      let p = BC.alloc #ctr #box {
        key = x;
        prev = Some t;
        next = (None #(box (node box a)))
      };
      BC.write #ctr #box t { nd with next = Some p };
      rewrite (bc.BC.pts_to t (hide { nd with next = Some p }))
        as (bc.BC.pts_to t (hide { key = last; prev = tail_prev; next = Some p }));
      fold (node_owns #ctr #box t tail_prev last (Some p));
      prefix_snoc #ctr #box #bc #a xs.head None #pre t tail_prev last p;
      fold (node_owns #ctr #box p (Some t) x None);
      close_last #ctr #box #bc #a xs.head None #(LLC.snoc pre last) (Some t) p x;
      rewrite (chain #ctr #box xs.head None (LLC.snoc (LLC.snoc pre last) x) (Some p))
        as (chain #ctr #box xs.head None (LLC.snoc l x) (Some p));
      rewrite (chain #ctr #box xs.head None (LLC.snoc l x) (Some p))
        as (owns #ctr #box { head = xs.head; tail = Some p } (LLC.snoc l x));
      { head = xs.head; tail = Some p }
    }
  }
}

fn rec search_chain
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (h:dptr box a)
    (prev:dptr box a)
    (tail:dptr box a)
    (same:a -> a -> Tot bool)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires chain #ctr #box h prev l tail ** MR.pts_to ctr #1.0R i
  returns found:bool
  ensures exists* ticks.
    chain #ctr #box h prev l tail **
    MR.pts_to ctr #1.0R ticks **
    pure (found <==> LLC.mem_by same x l /\ ticks <= i + search_bound (L.length l))
  decreases L.length l
{
  match h {
    None -> {
      chain_none_nil #ctr #box #bc #a prev tail #l;
      unfold (chain #ctr #box None prev l tail);
      rewrite each l as ([] #a);
      fold (chain #ctr #box None prev ([] #a) tail);
      rewrite (chain #ctr #box None prev ([] #a) tail)
        as (chain #ctr #box h prev l tail);
      false
    }
    Some p -> {
      chain_some_cons #ctr #box #bc #a p prev tail #l;
      rewrite each l as (L.hd l :: L.tl l) in (chain #ctr #box (Some p) prev l tail);
      unfold (chain #ctr #box (Some p) prev (L.hd l :: L.tl l) tail);
      with p0 nxt. _;
      rewrite each p0 as p;
      unfold (node_owns #ctr #box p prev (L.hd l) nxt);
      let nd = BC.read #ctr #box p;
      assert (pure (nd.key == L.hd l));
      assert (pure (nd.prev == prev));
      assert (pure (nd.next == nxt));
      rewrite (chain #ctr #box nxt (Some p) (L.tl l) tail)
        as (chain #ctr #box nd.next (Some p) (L.tl l) tail);
      if same x nd.key {
        fold (node_owns #ctr #box p prev (L.hd l) nxt);
        rewrite (node_owns #ctr #box p prev (L.hd l) nxt)
          as (node_owns #ctr #box p prev nd.key nd.next);
        fold (chain #ctr #box (Some p) prev (nd.key :: L.tl l) tail);
        rewrite (chain #ctr #box (Some p) prev (nd.key :: L.tl l) tail)
          as (chain #ctr #box h prev l tail);
        true
      } else {
        fold (node_owns #ctr #box p prev (L.hd l) nxt);
        rewrite (node_owns #ctr #box p prev (L.hd l) nxt)
          as (node_owns #ctr #box p prev nd.key nd.next);
        let found = search_chain ctr box #bc a nd.next (Some p) tail same x;
        fold (chain #ctr #box (Some p) prev (nd.key :: L.tl l) tail);
        rewrite (chain #ctr #box (Some p) prev (nd.key :: L.tl l) tail)
          as (chain #ctr #box h prev l tail);
        found
      }
    }
  }
}

fn search
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (xs:dll box a)
    (same:a -> a -> Tot bool)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires owns #ctr #box xs l ** MR.pts_to ctr #1.0R i
  returns found:bool
  ensures exists* ticks.
    owns #ctr #box xs l **
    MR.pts_to ctr #1.0R ticks **
    pure (found <==> LLC.mem_by same x l /\ ticks <= i + search_bound (L.length l))
{
  rewrite (owns #ctr #box xs l) as (chain #ctr #box xs.head None l xs.tail);
  let r = search_chain ctr box #bc a xs.head None xs.tail same x;
  rewrite (chain #ctr #box xs.head None l xs.tail) as (owns #ctr #box xs l);
  r
}

fn rec delete_first_chain
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (h:dptr box a)
    (prev:dptr box a)
    (tail:dptr box a)
    (same:a -> a -> Tot bool)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires chain #ctr #box h prev l tail ** MR.pts_to ctr #1.0R i
  returns xs':dll box a
  ensures exists* ticks.
    chain #ctr #box xs'.head prev (LLC.remove_first_by same x l) xs'.tail **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks <= i + delete_first_bound (L.length l))
  decreases L.length l
{
  match h {
    None -> {
      chain_none_nil #ctr #box #bc #a prev tail #l;
      unfold (chain #ctr #box None prev l tail);
      rewrite each l as ([] #a);
      fold (chain #ctr #box None prev ([] #a) tail);
      rewrite (chain #ctr #box None prev ([] #a) tail)
        as (chain #ctr #box None prev (LLC.remove_first_by same x l) tail);
      { head = None; tail = tail }
    }
    Some p -> {
      chain_some_cons #ctr #box #bc #a p prev tail #l;
      rewrite each l as (L.hd l :: L.tl l) in (chain #ctr #box (Some p) prev l tail);
      unfold (chain #ctr #box (Some p) prev (L.hd l :: L.tl l) tail);
      with p0 nxt. _;
      rewrite each p0 as p;
      unfold (node_owns #ctr #box p prev (L.hd l) nxt);
      let nd = BC.read #ctr #box p;
      assert (pure (nd.key == L.hd l));
      assert (pure (nd.prev == prev));
      assert (pure (nd.next == nxt));
      rewrite (chain #ctr #box nxt (Some p) (L.tl l) tail)
        as (chain #ctr #box nd.next (Some p) (L.tl l) tail);
      if same x nd.key {
        match nd.next {
          None -> {
            chain_none_nil #ctr #box #bc #a (Some p) tail #(L.tl l);
            BC.free #ctr #box p;
            unfold (chain #ctr #box None (Some p) (L.tl l) tail);
            rewrite each (L.tl l) as ([] #a);
            fold (chain #ctr #box None prev ([] #a) prev);
            rewrite (chain #ctr #box None prev ([] #a) prev)
              as (chain #ctr #box None prev (LLC.remove_first_by same x l) prev);
            { head = None; tail = prev }
          }
          Some q -> {
            chain_some_cons #ctr #box #bc #a q (Some p) tail #(L.tl l);
            set_first_prev #ctr #box #bc #a q (Some p) prev #(L.tl l) tail;
            BC.free #ctr #box p;
            rewrite (chain #ctr #box (Some q) prev (L.tl l) tail)
              as (chain #ctr #box (Some q) prev (LLC.remove_first_by same x l) tail);
            { head = Some q; tail = tail }
          }
        }
      } else {
        fold (node_owns #ctr #box p prev (L.hd l) nxt);
        let r = delete_first_chain ctr box #bc a nd.next (Some p) tail same x;
        unfold (node_owns #ctr #box p prev (L.hd l) nxt);
        BC.write #ctr #box p { nd with next = r.head };
        rewrite (bc.BC.pts_to p (hide { nd with next = r.head }))
          as (bc.BC.pts_to p (hide { key = nd.key; prev = prev; next = r.head }));
        fold (node_owns #ctr #box p prev nd.key r.head);
        fold (chain #ctr #box (Some p) prev (nd.key :: LLC.remove_first_by same x (L.tl l)) r.tail);
        rewrite (chain #ctr #box (Some p) prev (nd.key :: LLC.remove_first_by same x (L.tl l)) r.tail)
          as (chain #ctr #box (Some p) prev (LLC.remove_first_by same x l) r.tail);
        { head = Some p; tail = r.tail }
      }
    }
  }
}

fn delete_first
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (xs:dll box a)
    (same:a -> a -> Tot bool)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires owns #ctr #box xs l ** MR.pts_to ctr #1.0R i
  returns xs':dll box a
  ensures exists* ticks.
    owns #ctr #box xs' (LLC.remove_first_by same x l) **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks <= i + delete_first_bound (L.length l))
{
  rewrite (owns #ctr #box xs l) as (chain #ctr #box xs.head None l xs.tail);
  let r = delete_first_chain ctr box #bc a xs.head None xs.tail same x;
  rewrite (chain #ctr #box r.head None (LLC.remove_first_by same x l) r.tail)
    as (owns #ctr #box r (LLC.remove_first_by same x l));
  r
}

fn rec delete_last_chain
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (h:dptr box a)
    (prev:dptr box a)
    (tail:dptr box a)
    (same:a -> a -> Tot bool)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires chain #ctr #box h prev l tail ** MR.pts_to ctr #1.0R i
  returns r:(dll box a & bool)
  ensures exists* ticks.
    chain #ctr #box (fst r).head prev (LLC.remove_last_by same x l) (fst r).tail **
    MR.pts_to ctr #1.0R ticks **
    pure (snd r == LLC.mem_by same x l /\ ticks <= i + delete_last_bound (L.length l))
  decreases L.length l
{
  match h {
    None -> {
      chain_none_nil #ctr #box #bc #a prev tail #l;
      unfold (chain #ctr #box None prev l tail);
      rewrite each l as ([] #a);
      fold (chain #ctr #box None prev ([] #a) tail);
      rewrite (chain #ctr #box None prev ([] #a) tail)
        as (chain #ctr #box None prev (LLC.remove_last_by same x l) tail);
      ({ head = None; tail = tail }, false)
    }
    Some p -> {
      chain_some_cons #ctr #box #bc #a p prev tail #l;
      rewrite each l as (L.hd l :: L.tl l) in (chain #ctr #box (Some p) prev l tail);
      unfold (chain #ctr #box (Some p) prev (L.hd l :: L.tl l) tail);
      with p0 nxt. _;
      rewrite each p0 as p;
      unfold (node_owns #ctr #box p prev (L.hd l) nxt);
      let nd = BC.read #ctr #box p;
      assert (pure (nd.key == L.hd l));
      assert (pure (nd.prev == prev));
      assert (pure (nd.next == nxt));
      rewrite (chain #ctr #box nxt (Some p) (L.tl l) tail)
        as (chain #ctr #box nd.next (Some p) (L.tl l) tail);
      let r = delete_last_chain ctr box #bc a nd.next (Some p) tail same x;
      let xs_tail = fst r;
      let removed = snd r;
      rewrite (chain #ctr #box (fst r).head (Some p) (LLC.remove_last_by same x (L.tl l)) (fst r).tail)
        as (chain #ctr #box xs_tail.head (Some p) (LLC.remove_last_by same x (L.tl l)) xs_tail.tail);
      assert (pure (removed == LLC.mem_by same x (L.tl l)));
      if removed {
        remove_last_cons_tail_hit same x nd.key (L.tl l);
        BC.write #ctr #box p { nd with next = xs_tail.head };
        rewrite (bc.BC.pts_to p (hide { nd with next = xs_tail.head }))
          as (bc.BC.pts_to p (hide { key = nd.key; prev = prev; next = xs_tail.head }));
        fold (node_owns #ctr #box p prev nd.key xs_tail.head);
        fold (chain #ctr #box (Some p) prev (nd.key :: LLC.remove_last_by same x (L.tl l)) xs_tail.tail);
        rewrite (chain #ctr #box (Some p) prev (nd.key :: LLC.remove_last_by same x (L.tl l)) xs_tail.tail)
          as (chain #ctr #box (Some p) prev (LLC.remove_last_by same x l) xs_tail.tail);
        ({ head = Some p; tail = xs_tail.tail }, true)
      } else if same x nd.key {
        remove_last_cons_head_hit same x nd.key (L.tl l);
        remove_last_no_mem same x (L.tl l);
        rewrite (chain #ctr #box xs_tail.head (Some p) (LLC.remove_last_by same x (L.tl l)) xs_tail.tail)
          as (chain #ctr #box xs_tail.head (Some p) (L.tl l) xs_tail.tail);
        match xs_tail.head {
          None -> {
            chain_none_nil #ctr #box #bc #a (Some p) xs_tail.tail #(L.tl l);
            BC.free #ctr #box p;
            unfold (chain #ctr #box None (Some p) (L.tl l) xs_tail.tail);
            rewrite each (L.tl l) as ([] #a);
            fold (chain #ctr #box None prev ([] #a) prev);
            rewrite (chain #ctr #box None prev ([] #a) prev)
              as (chain #ctr #box None prev (LLC.remove_last_by same x l) prev);
            ({ head = None; tail = prev }, true)
          }
          Some q -> {
            chain_some_cons #ctr #box #bc #a q (Some p) xs_tail.tail #(L.tl l);
            set_first_prev #ctr #box #bc #a q (Some p) prev #(L.tl l) xs_tail.tail;
            BC.free #ctr #box p;
            rewrite (chain #ctr #box (Some q) prev (L.tl l) xs_tail.tail)
              as (chain #ctr #box (Some q) prev (LLC.remove_last_by same x l) xs_tail.tail);
            ({ head = Some q; tail = xs_tail.tail }, true)
          }
        }
      } else {
        remove_last_cons_miss same x nd.key (L.tl l);
        remove_last_no_mem same x (L.tl l);
        rewrite (chain #ctr #box xs_tail.head (Some p) (LLC.remove_last_by same x (L.tl l)) xs_tail.tail)
          as (chain #ctr #box xs_tail.head (Some p) (L.tl l) xs_tail.tail);
        BC.write #ctr #box p { nd with next = xs_tail.head };
        rewrite (bc.BC.pts_to p (hide { nd with next = xs_tail.head }))
          as (bc.BC.pts_to p (hide { key = nd.key; prev = prev; next = xs_tail.head }));
        fold (node_owns #ctr #box p prev nd.key xs_tail.head);
        fold (chain #ctr #box (Some p) prev (nd.key :: L.tl l) xs_tail.tail);
        rewrite (chain #ctr #box (Some p) prev (nd.key :: L.tl l) xs_tail.tail)
          as (chain #ctr #box (Some p) prev (LLC.remove_last_by same x l) xs_tail.tail);
        ({ head = Some p; tail = xs_tail.tail }, false)
      }
    }
  }
}

fn delete_last
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (xs:dll box a)
    (same:a -> a -> Tot bool)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires owns #ctr #box xs l ** MR.pts_to ctr #1.0R i
  returns xs':dll box a
  ensures exists* ticks.
    owns #ctr #box xs' (LLC.remove_last_by same x l) **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks <= i + delete_last_bound (L.length l))
{
  rewrite (owns #ctr #box xs l) as (chain #ctr #box xs.head None l xs.tail);
  let r = delete_last_chain ctr box #bc a xs.head None xs.tail same x;
  let xs' = fst r;
  rewrite (chain #ctr #box (fst r).head None (LLC.remove_last_by same x l) (fst r).tail)
    as (chain #ctr #box xs'.head None (LLC.remove_last_by same x l) xs'.tail);
  rewrite (chain #ctr #box xs'.head None (LLC.remove_last_by same x l) xs'.tail)
    as (owns #ctr #box xs' (LLC.remove_last_by same x l));
  xs'
}

instance dll_structure
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
  : LLC.linked_list_structure
      ctr
      box
      #bc
      a
      (dll box a)
      (owns #ctr #box)
      insert_head_bound
      append_tail_bound
      search_bound
      delete_first_bound
      delete_last_bound
= {
  insert_head = insert_head ctr box #bc a;
  append_tail = append_tail ctr box #bc a;
  search = search ctr box #bc a;
  delete_first = delete_first ctr box #bc a;
  delete_last = delete_last ctr box #bc a
}
