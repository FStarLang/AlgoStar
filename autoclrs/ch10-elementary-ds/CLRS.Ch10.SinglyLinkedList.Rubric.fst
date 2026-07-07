module CLRS.Ch10.SinglyLinkedList.Rubric
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
  next: option (box (node box a));
}

let dlist
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    (a:Type0)
  : Type0
  = option (box (node box a))

let rec owns
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (head:dlist box a)
    (l:list a)
  : Tot slprop (decreases L.length l)
  = match l with
    | [] -> pure (head == None)
    | hd :: tl ->
      exists* (p:box (node box a)) (tail:dlist box a).
        pure (head == Some p) **
        bc.BC.pts_to p (hide { key = hd; next = tail }) **
        owns #ctr #box tail tl

ghost
fn owns_none_nil
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (#l:erased (list a))
  preserves owns #ctr #box None l
  ensures pure (l == [])
{
  let ll = reveal l;
  match ll {
    [] -> { () }
    hd :: tl -> {
      rewrite each l as (hd :: tl) in (owns #ctr #box None l);
      unfold (owns #ctr #box None (hd :: tl));
      unreachable ()
    }
  }
}

ghost
fn owns_some_cons
    (#ctr:BC.ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (#a:Type0)
    (p:box (node box a))
    (#l:erased (list a))
  preserves owns #ctr #box (Some p) l
  ensures pure (Cons? l)
{
  let ll = reveal l;
  match ll {
    [] -> {
      rewrite each l as ([] #a) in (owns #ctr #box (Some p) l);
      unfold (owns #ctr #box (Some p) ([] #a));
      unreachable ()
    }
    hd :: tl -> { () }
  }
}

let insert_head_bound (_n:nat) : nat = BC.alloc_cost
let append_tail_bound (n:nat) : nat = 2 * n + BC.alloc_cost
let search_bound (n:nat) : nat = n
let delete_first_bound (n:nat) : nat = 2 * n + BC.free_cost
let delete_last_bound (n:nat) : nat = 2 * n + BC.free_cost

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

fn insert_head
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (head:dlist box a)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires owns #ctr #box head l ** MR.pts_to ctr #1.0R i
  returns head':dlist box a
  ensures exists* ticks.
    owns #ctr #box head' (x :: l) **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks <= i + insert_head_bound (L.length l))
{
  let p = BC.alloc #ctr #box { key = x; next = head };
  fold (owns #ctr #box (Some p) (x :: l));
  Some p
}

fn rec append_tail
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (head:dlist box a)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires owns #ctr #box head l ** MR.pts_to ctr #1.0R i
  returns head':dlist box a
  ensures exists* ticks.
    owns #ctr #box head' (LLC.snoc l x) **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks <= i + append_tail_bound (L.length l))
  decreases L.length l
{
  match head {
    None -> {
      owns_none_nil #ctr #box #bc #a #l;
      unfold (owns #ctr #box None l);
      rewrite each l as ([] #a);
      fold (owns #ctr #box None ([] #a));
      let p = BC.alloc #ctr #box { key = x; next = (None #(box (node box a))) };
      fold (owns #ctr #box (Some p) [x]);
      rewrite (owns #ctr #box (Some p) [x])
        as (owns #ctr #box (Some p) (LLC.snoc l x));
      Some p
    }
    Some p -> {
      owns_some_cons #ctr #box #bc #a p #l;
      rewrite each l as (L.hd l :: L.tl l) in (owns #ctr #box (Some p) l);
      unfold (owns #ctr #box (Some p) (L.hd l :: L.tl l));
      with p0 tail. _;
      rewrite each p0 as p;
      let nd = BC.read #ctr #box p;
      assert (pure (nd.key == L.hd l));
      assert (pure (nd.next == tail));
      rewrite (owns #ctr #box tail (L.tl l)) as (owns #ctr #box nd.next (L.tl l));
      let tail' = append_tail ctr box #bc a nd.next x;
      BC.write #ctr #box p { nd with next = tail' };
      fold (owns #ctr #box (Some p) (nd.key :: LLC.snoc (L.tl l) x));
      rewrite (owns #ctr #box (Some p) (nd.key :: LLC.snoc (L.tl l) x))
        as (owns #ctr #box (Some p) (LLC.snoc l x));
      Some p
    }
  }
}

fn rec search
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (head:dlist box a)
    (same:a -> a -> Tot bool)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires owns #ctr #box head l ** MR.pts_to ctr #1.0R i
  returns found:bool
  ensures exists* ticks.
    owns #ctr #box head l **
    MR.pts_to ctr #1.0R ticks **
    pure (found <==> LLC.mem_by same x l /\ ticks <= i + search_bound (L.length l))
  decreases L.length l
{
  match head {
    None -> {
      owns_none_nil #ctr #box #bc #a #l;
      unfold (owns #ctr #box None l);
      rewrite each l as ([] #a);
      fold (owns #ctr #box None ([] #a));
      rewrite (owns #ctr #box None ([] #a)) as (owns #ctr #box head l);
      false
    }
    Some p -> {
      owns_some_cons #ctr #box #bc #a p #l;
      rewrite each l as (L.hd l :: L.tl l) in (owns #ctr #box (Some p) l);
      unfold (owns #ctr #box (Some p) (L.hd l :: L.tl l));
      with p0 tail. _;
      rewrite each p0 as p;
      let nd = BC.read #ctr #box p;
      assert (pure (nd.key == L.hd l));
      assert (pure (nd.next == tail));
      rewrite (owns #ctr #box tail (L.tl l)) as (owns #ctr #box nd.next (L.tl l));
      rewrite (bc.BC.pts_to p (hide { key = L.hd l; next = tail }))
        as (bc.BC.pts_to p (hide { key = nd.key; next = nd.next }));
      if same x nd.key {
        fold (owns #ctr #box (Some p) (nd.key :: L.tl l));
        rewrite (owns #ctr #box (Some p) (nd.key :: L.tl l)) as (owns #ctr #box head l);
        true
      } else {
        let found = search ctr box #bc a nd.next same x;
        fold (owns #ctr #box (Some p) (nd.key :: L.tl l));
        rewrite (owns #ctr #box (Some p) (nd.key :: L.tl l)) as (owns #ctr #box head l);
        found
      }
    }
  }
}

fn rec delete_first
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (head:dlist box a)
    (same:a -> a -> Tot bool)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires owns #ctr #box head l ** MR.pts_to ctr #1.0R i
  returns head':dlist box a
  ensures exists* ticks.
    owns #ctr #box head' (LLC.remove_first_by same x l) **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks <= i + delete_first_bound (L.length l))
  decreases L.length l
{
  match head {
    None -> {
      owns_none_nil #ctr #box #bc #a #l;
      unfold (owns #ctr #box None l);
      rewrite each l as ([] #a);
      fold (owns #ctr #box None ([] #a));
      rewrite (owns #ctr #box None ([] #a))
        as (owns #ctr #box head (LLC.remove_first_by same x l));
      head
    }
    Some p -> {
      owns_some_cons #ctr #box #bc #a p #l;
      rewrite each l as (L.hd l :: L.tl l) in (owns #ctr #box (Some p) l);
      unfold (owns #ctr #box (Some p) (L.hd l :: L.tl l));
      with p0 tail. _;
      rewrite each p0 as p;
      let nd = BC.read #ctr #box p;
      assert (pure (nd.key == L.hd l));
      assert (pure (nd.next == tail));
      rewrite (owns #ctr #box tail (L.tl l)) as (owns #ctr #box nd.next (L.tl l));
      if same x nd.key {
        BC.free #ctr #box p;
        rewrite (owns #ctr #box nd.next (L.tl l))
          as (owns #ctr #box nd.next (LLC.remove_first_by same x l));
        nd.next
      } else {
        let tail' = delete_first ctr box #bc a nd.next same x;
        BC.write #ctr #box p { nd with next = tail' };
        fold (owns #ctr #box (Some p) (nd.key :: LLC.remove_first_by same x (L.tl l)));
        rewrite (owns #ctr #box (Some p) (nd.key :: LLC.remove_first_by same x (L.tl l)))
          as (owns #ctr #box (Some p) (LLC.remove_first_by same x l));
        Some p
      }
    }
  }
}

fn rec delete_last_aux
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (head:dlist box a)
    (same:a -> a -> Tot bool)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires owns #ctr #box head l ** MR.pts_to ctr #1.0R i
  returns r:(dlist box a & bool)
  ensures exists* ticks.
    owns #ctr #box (fst r) (LLC.remove_last_by same x l) **
    MR.pts_to ctr #1.0R ticks **
    pure (snd r == LLC.mem_by same x l /\ ticks <= i + delete_last_bound (L.length l))
  decreases L.length l
{
  match head {
    None -> {
      owns_none_nil #ctr #box #bc #a #l;
      unfold (owns #ctr #box None l);
      rewrite each l as ([] #a);
      fold (owns #ctr #box None ([] #a));
      rewrite (owns #ctr #box None ([] #a))
        as (owns #ctr #box head (LLC.remove_last_by same x l));
      (head, false)
    }
    Some p -> {
      owns_some_cons #ctr #box #bc #a p #l;
      rewrite each l as (L.hd l :: L.tl l) in (owns #ctr #box (Some p) l);
      unfold (owns #ctr #box (Some p) (L.hd l :: L.tl l));
      with p0 tail. _;
      rewrite each p0 as p;
      let nd = BC.read #ctr #box p;
      assert (pure (nd.key == L.hd l));
      assert (pure (nd.next == tail));
      rewrite (owns #ctr #box tail (L.tl l)) as (owns #ctr #box nd.next (L.tl l));
      let r = delete_last_aux ctr box #bc a nd.next same x;
      let tail' = fst r;
      let removed = snd r;
      rewrite (owns #ctr #box (fst r) (LLC.remove_last_by same x (L.tl l)))
        as (owns #ctr #box tail' (LLC.remove_last_by same x (L.tl l)));
      assert (pure (removed == LLC.mem_by same x (L.tl l)));
      if removed {
        remove_last_cons_tail_hit same x nd.key (L.tl l);
        BC.write #ctr #box p { nd with next = tail' };
        fold (owns #ctr #box (Some p) (nd.key :: LLC.remove_last_by same x (L.tl l)));
        rewrite (owns #ctr #box (Some p) (nd.key :: LLC.remove_last_by same x (L.tl l)))
          as (owns #ctr #box (Some p) (LLC.remove_last_by same x l));
        (Some p, true)
      } else if same x nd.key {
        remove_last_cons_head_hit same x nd.key (L.tl l);
        BC.free #ctr #box p;
        rewrite (owns #ctr #box tail' (LLC.remove_last_by same x (L.tl l)))
          as (owns #ctr #box tail' (L.tl l));
        rewrite (owns #ctr #box tail' (L.tl l))
          as (owns #ctr #box tail' (LLC.remove_last_by same x l));
        (tail', true)
      } else {
        remove_last_cons_miss same x nd.key (L.tl l);
        rewrite (owns #ctr #box tail' (LLC.remove_last_by same x (L.tl l)))
          as (owns #ctr #box tail' (L.tl l));
        BC.write #ctr #box p { nd with next = tail' };
        fold (owns #ctr #box (Some p) (nd.key :: L.tl l));
        rewrite (owns #ctr #box (Some p) (nd.key :: L.tl l))
          as (owns #ctr #box (Some p) (LLC.remove_last_by same x l));
        (Some p, false)
      }
    }
  }
}

fn delete_last
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
    (head:dlist box a)
    (same:a -> a -> Tot bool)
    (x:a)
    (#l:erased (list a))
    (#i:erased nat)
  requires owns #ctr #box head l ** MR.pts_to ctr #1.0R i
  returns head':dlist box a
  ensures exists* ticks.
    owns #ctr #box head' (LLC.remove_last_by same x l) **
    MR.pts_to ctr #1.0R ticks **
    pure (ticks <= i + delete_last_bound (L.length l))
{
  let r = delete_last_aux ctr box #bc a head same x;
  fst r
}

instance sll
    (ctr:BC.ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| bc:BC.box_class ctr box |}
    (a:Type0)
  : LLC.linked_list_structure
      ctr
      box
      #bc
      a
      (dlist box a)
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
