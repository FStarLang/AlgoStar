(**
 * ISMM: Status type for the reference counting algorithm.
 *
 * Paper: "Reference Counting Deeply Immutable Data Structures with Cycles"
 *        Parkinson, Clebsch, Wrigstad — ISMM '24
 *
 * Defines the 4-state node status (Section 3, Fig. 2):
 *   UNMARKED — not yet visited by freeze
 *   RANK(n)  — on pending stack; UF rank = n
 *   REP(ptr) — UF non-root; representative reachable via ptr
 *   RC(n)    — SCC representative; external reference count = n
 *
 * Encoded as two parallel int arrays (tag + data) for Pulse compatibility.
 *)
module ISMM.Status

module Seq = FStar.Seq

(*** Status tag constants ***)

let tag_unmarked : int = 0
let tag_rank     : int = 1
let tag_rep      : int = 2
let tag_rc       : int = 3

(*** Status predicates on ghost sequences ***)

let valid_tag (t: int) : bool =
  t = tag_unmarked || t = tag_rank || t = tag_rep || t = tag_rc

let is_unmarked (stag: Seq.seq int) (i: nat) : prop =
  i < Seq.length stag /\ Seq.index stag i == tag_unmarked

let is_rank (stag: Seq.seq int) (i: nat) : prop =
  i < Seq.length stag /\ Seq.index stag i == tag_rank

let is_rep (stag: Seq.seq int) (i: nat) : prop =
  i < Seq.length stag /\ Seq.index stag i == tag_rep

let is_rc (stag: Seq.seq int) (i: nat) : prop =
  i < Seq.length stag /\ Seq.index stag i == tag_rc

/// A node is "frozen" if it is part of a completed SCC (REP or RC).
let is_frozen (stag: Seq.seq int) (i: nat) : prop =
  is_rep stag i \/ is_rc stag i

/// Valid status tags throughout an array of size n.
let all_valid_tags (stag: Seq.seq int) (n: nat) : prop =
  n <= Seq.length stag /\
  (forall (i: nat). i < n ==> valid_tag (Seq.index stag i))

/// All nodes in [0, n) are UNMARKED.
let all_unmarked (stag: Seq.seq int) (n: nat) : prop =
  n <= Seq.length stag /\
  (forall (i: nat). i < n ==> is_unmarked stag i)
