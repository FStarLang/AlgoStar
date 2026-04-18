(**
   Spec validation test for CLRS.Ch10.DLL.Impl — CLRS §10.2.

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        Ghost assert(pure(...)) statements verify correctness at proof time.
     2. RUNTIME (computational, survives extraction to C):
        bool_eq comparisons and Some?/None? checks survive extraction.
        Returns bool — caller can verify at runtime.

   Split into per-scenario functions to reduce peak memory usage during
   verification (avoids quadratic lambda-bloat in the unifier — see
   tmp/memory_profile.md for root cause analysis).

   No admits. No assumes.
*)
module CLRS.Ch10.DLL.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch10.DLL.Impl
module L = FStar.List.Tot

inline_for_extraction
let bool_eq (a b: bool) : (r:bool{r <==> a = b}) = (a = b)

```pulse
(** Scenario 1 — insert at head:
    Insert 3, 2, 1 at head → list is [1; 2; 3].
    Search forward for 2 → true, for 99 → false.
    Search backward for 3 → true, for 0 → false.
    Delete 2 → list is [1; 3].
    Search for 2 → false.
    Delete 1, delete 3 → empty. *)
fn test_insert_head ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  let mut hd_ref : dptr = None;
  let mut tl_ref : dptr = None;
  dll_nil None None;

  list_insert hd_ref tl_ref 3;
  list_insert hd_ref tl_ref 2;
  list_insert hd_ref tl_ref 1;

  let hd1 = !hd_ref;
  let tl1 = !tl_ref;

  let found2 = list_search hd1 tl1 2;
  assert (pure (found2 == true));
  let pass = bool_eq found2 true;

  let not99 = list_search hd1 tl1 99;
  assert (pure (not99 == false));
  let pass = pass && bool_eq not99 false;

  let found3_back = list_search_back hd1 tl1 3;
  assert (pure (found3_back == true));
  let pass = pass && bool_eq found3_back true;

  let not0_back = list_search_back hd1 tl1 0;
  assert (pure (not0_back == false));
  let pass = pass && bool_eq not0_back false;

  let ptr1 = list_search_ptr hd1 tl1 1;
  assert (pure (Some? ptr1));
  let pass = pass && (Some? ptr1);

  let ptr42 = list_search_ptr hd1 tl1 42;
  assert (pure (None? ptr42));
  let pass = pass && (None? ptr42);

  list_delete hd_ref tl_ref 2;
  list_delete hd_ref tl_ref 99;

  let hd2 = !hd_ref;
  let tl2 = !tl_ref;
  let gone2 = list_search hd2 tl2 2;
  assert (pure (gone2 == false));
  let pass = pass && bool_eq gone2 false;

  let still1 = list_search hd2 tl2 1;
  assert (pure (still1 == true));
  let pass = pass && bool_eq still1 true;
  let still3 = list_search hd2 tl2 3;
  assert (pure (still3 == true));
  let pass = pass && bool_eq still3 true;

  list_delete hd_ref tl_ref 1;
  list_delete hd_ref tl_ref 3;

  with hd_empty tl_empty.
    assert (pts_to hd_ref hd_empty ** pts_to tl_ref tl_empty ** dll hd_empty tl_empty _);
  dll_nil_elim hd_empty tl_empty;
  assert (pure (hd_empty == None /\ tl_empty == None));

  pass
}
```

```pulse
(** Scenario 2 — insert at tail:
    Insert 10 at head, insert 20 at tail, insert 30 at tail → [10; 20; 30].
    Verify via search.
    Delete all. *)
fn test_insert_tail ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  let mut hd_ref : dptr = None;
  let mut tl_ref : dptr = None;
  dll_nil None None;

  list_insert hd_ref tl_ref 10;
  list_insert_tail hd_ref tl_ref 20;
  list_insert_tail hd_ref tl_ref 30;

  let hd3 = !hd_ref;
  let tl3 = !tl_ref;

  let f10 = list_search hd3 tl3 10;
  assert (pure (f10 == true));
  let pass = bool_eq f10 true;
  let f20 = list_search hd3 tl3 20;
  assert (pure (f20 == true));
  let pass = pass && bool_eq f20 true;
  let f30 = list_search hd3 tl3 30;
  assert (pure (f30 == true));
  let pass = pass && bool_eq f30 true;
  let f99 = list_search hd3 tl3 99;
  assert (pure (f99 == false));
  let pass = pass && bool_eq f99 false;

  list_delete hd_ref tl_ref 10;
  list_delete hd_ref tl_ref 20;
  list_delete hd_ref tl_ref 30;

  with hd_fin tl_fin.
    assert (pts_to hd_ref hd_fin ** pts_to tl_ref tl_fin ** dll hd_fin tl_fin _);
  drop_ (dll hd_fin tl_fin _);

  pass
}
```

```pulse
(** Scenario 3 — list_delete_last:
    Build [1; 2; 1; 3], delete_last 1 → [1; 2; 3]. *)
fn test_delete_last ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  let mut hd_ref : dptr = None;
  let mut tl_ref : dptr = None;
  dll_nil None None;

  list_insert hd_ref tl_ref 3;
  list_insert hd_ref tl_ref 1;
  list_insert hd_ref tl_ref 2;
  list_insert hd_ref tl_ref 1;

  list_delete_last hd_ref tl_ref 1;

  let hd4 = !hd_ref;
  let tl4 = !tl_ref;
  let f1_s3 = list_search hd4 tl4 1;
  assert (pure (f1_s3 == true));
  let pass = bool_eq f1_s3 true;
  let f2_s3 = list_search hd4 tl4 2;
  assert (pure (f2_s3 == true));
  let pass = pass && bool_eq f2_s3 true;
  let f3_s3 = list_search hd4 tl4 3;
  assert (pure (f3_s3 == true));
  let pass = pass && bool_eq f3_s3 true;

  list_delete_last hd_ref tl_ref 99;

  let hd4b = !hd_ref;
  let tl4b = !tl_ref;
  let f1_s3b = list_search hd4b tl4b 1;
  assert (pure (f1_s3b == true));
  let pass = pass && bool_eq f1_s3b true;

  list_delete hd_ref tl_ref 1;
  list_delete hd_ref tl_ref 2;
  list_delete hd_ref tl_ref 3;

  with hd_fin tl_fin.
    assert (pts_to hd_ref hd_fin ** pts_to tl_ref tl_fin ** dll hd_fin tl_fin _);
  drop_ (dll hd_fin tl_fin _);

  pass
}
```

```pulse
(** Scenario 4 — list_delete_node (delete by index):
    Build [10; 20; 30], delete at index 1 → [10; 30], etc. *)
fn test_delete_node ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  let mut hd_ref : dptr = None;
  let mut tl_ref : dptr = None;
  dll_nil None None;

  list_insert hd_ref tl_ref 30;
  list_insert hd_ref tl_ref 20;
  list_insert hd_ref tl_ref 10;

  list_delete_node hd_ref tl_ref 1;

  let hd5 = !hd_ref;
  let tl5 = !tl_ref;
  let f10_s4 = list_search hd5 tl5 10;
  assert (pure (f10_s4 == true));
  let pass = bool_eq f10_s4 true;
  let f30_s4 = list_search hd5 tl5 30;
  assert (pure (f30_s4 == true));
  let pass = pass && bool_eq f30_s4 true;
  let f20_s4 = list_search hd5 tl5 20;
  assert (pure (f20_s4 == false));
  let pass = pass && bool_eq f20_s4 false;

  list_delete_node hd_ref tl_ref 0;

  let hd6 = !hd_ref;
  let tl6 = !tl_ref;
  let f30_s4b = list_search hd6 tl6 30;
  assert (pure (f30_s4b == true));
  let pass = pass && bool_eq f30_s4b true;
  let f10_s4b = list_search hd6 tl6 10;
  assert (pure (f10_s4b == false));
  let pass = pass && bool_eq f10_s4b false;

  list_delete_node hd_ref tl_ref 0;

  with hd_e tl_e.
    assert (pts_to hd_ref hd_e ** pts_to tl_ref tl_e ** dll hd_e tl_e _);
  dll_nil_elim hd_e tl_e;
  assert (pure (hd_e == None /\ tl_e == None));

  pass
}
```

```pulse
(** Main spec-validation test — runs all four scenarios. *)
fn test_dll_spec_validation ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  let r1 = test_insert_head ();
  let r2 = test_insert_tail ();
  let r3 = test_delete_last ();
  let r4 = test_delete_node ();
  r1 && r2 && r3 && r4
}
```
