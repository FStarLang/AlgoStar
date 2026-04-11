module CLRS.Ch32.KMP.C.BridgeLemmas
open CLRS.Ch32.KMP.PureDefs
open CLRS.Ch32.KMP.Spec
module Seq = FStar.Seq
module SizeT = FStar.SizeT

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

let follow_fail_step pattern pi k c =
  pi_val_bounds pattern pi (k - 1);
  ()

let is_max_prefix_below_init text pattern n m =
  assert (matched_prefix_at text pattern 0 0);
  assert (forall (k:nat). matched_prefix_at text pattern 0 k /\ k < m ==> k <= 0)

#push-options "--z3rlimit 80"
let kmp_extend_connection pattern pi q_init q_final c m =
  ()
#pop-options

let unwrap_seq_index_lemma s m q = ()

let count_finish vt vp n m =
  let t = unwrap_int_seq vt n in
  let p = unwrap_int_seq vp m in
  assert (Seq.length t == n);
  assert (Seq.length p == m);
  count_before_eq_spec t p n m

#pop-options

/// ---- compute_prefix bridge lemma implementations ----
///
/// Strategy: pi_max_up_to_int is opaque. extend_maximality_int uses
/// PER-ELEMENT helpers (nonneg/valid/max_transfer_int) that each call
/// pi_max_instantiate_int or pi_max_max_at_int internally (tiny VCs).
/// No flat foralls from unfold_pi_max_int exist in the orchestrator's VC,
/// preventing the quantifier cascade that occurs when flat foralls
/// from unfold interact with fold's requires or goal quantifiers.

module Bridge = CLRS.Ch32.KMP.Bridge

let maximality_base_int pattern pi =
  reveal_opaque (`%pi_max_up_to_int) pi_max_up_to_int;
  assert (is_prefix_suffix #int pattern 0 0)

let pi_max_instantiate_int pattern pi bound r =
  reveal_opaque (`%pi_max_up_to_int) pi_max_up_to_int

let pi_max_max_at_int pattern pi bound r k =
  reveal_opaque (`%pi_max_up_to_int) pi_max_up_to_int

let inner_init_int pattern pi q k =
  reveal_opaque (`%pi_max_up_to_int) pi_max_up_to_int

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0 --split_queries always"
let inner_step_int pattern pi q k k_new =
  reveal_opaque (`%pi_max_up_to_int) pi_max_up_to_int;
  let aux (j: nat{j > k_new /\ is_prefix_suffix #int pattern (q - 1) j /\ j < Seq.length pattern})
    : Lemma (Seq.index pattern j <> Seq.index pattern q)
    = if j > k then ()
      else if j = k then ()
      else begin
        Bridge.ps_nesting_gen #int pattern (q - 1) k j;
        assert (is_prefix_suffix #int pattern (k - 1) j);
        assert (k - 1 < q);
        assert (j <= Seq.index pi (k - 1))
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
  failure_chain #int pattern (q - 1) k k_new
#pop-options

let unwrap_seq_update s m q v = ()

/// ---------- extend_maximality_int: per-element transfer approach ----------
/// Key insight: NEVER call unfold_pi_max_int. Instead, each per-element
/// transfer helper calls pi_max_instantiate_int or pi_max_max_at_int
/// internally (tiny VC with reveal_opaque). The orchestrator's VC has
/// NO flat foralls → no cascade source.

/// Fold flat foralls into opaque (tiny VC: just reveal + identity)
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let fold_pi_max_int (pattern pi: Seq.seq int) (bound: nat)
  : Lemma
    (requires bound <= Seq.length pattern /\
             Seq.length pi >= Seq.length pattern /\
             Seq.length pattern > 0 /\
             (forall (q: nat). q < bound ==> Seq.index pi q >= 0) /\
             (forall (q: nat). q < bound ==>
               is_prefix_suffix #int pattern q (Seq.index pi q)) /\
             (forall (q: nat) (k: nat). q < bound /\ is_prefix_suffix #int pattern q k ==>
               k <= Seq.index pi q))
    (ensures pi_max_up_to_int pattern pi bound)
  = reveal_opaque (`%pi_max_up_to_int) pi_max_up_to_int
#pop-options

/// Prove is_prefix_suffix at q when chars match
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
private let prove_validity_match_int (pattern: Seq.seq int)
    (q: nat{0 < q /\ q < Seq.length pattern}) (k_final: nat)
  : Lemma
    (requires is_prefix_suffix #int pattern (q - 1) k_final /\
             k_final < Seq.length pattern /\
             Seq.index pattern k_final == Seq.index pattern q)
    (ensures is_prefix_suffix #int pattern q (k_final + 1))
  = ()
#pop-options

/// Establish is_prefix_suffix at q about pi_new[q]
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
private let establish_validity_at_q_int (pattern pi_new: Seq.seq int)
    (q: nat{0 < q /\ q < Seq.length pattern}) (k_final: nat) (chars_match: bool)
  : Lemma
    (requires is_prefix_suffix #int pattern (q - 1) k_final /\
             k_final < Seq.length pattern /\
             (chars_match ==> Seq.index pattern k_final == Seq.index pattern q) /\
             (not chars_match ==> k_final == 0) /\
             Seq.length pi_new >= Seq.length pattern /\
             Seq.index pi_new q == (if chars_match then k_final + 1 else k_final) /\
             Seq.index pi_new q >= 0)
    (ensures is_prefix_suffix #int pattern q (Seq.index pi_new q))
  = if chars_match then begin
      prove_validity_match_int pattern q k_final;
      assert (Seq.index pi_new q == k_final + 1)
    end else begin
      assert (k_final == 0);
      assert (Seq.index pi_new q == 0);
      assert (is_prefix_suffix #int pattern q 0)
    end
#pop-options

/// Prove maximality at position q
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
private let maximality_at_q_int (pattern: Seq.seq int)
    (q: nat{0 < q /\ q < Seq.length pattern})
    (k_final: nat) (chars_match: bool) (j: nat)
  : Lemma
    (requires is_prefix_suffix #int pattern (q - 1) k_final /\
             k_final < Seq.length pattern /\
             Bridge.all_ps_above_mismatch #int pattern q k_final /\
             (chars_match ==> Seq.index pattern k_final == Seq.index pattern q) /\
             (not chars_match ==> (k_final == 0 /\ Seq.index pattern k_final <> Seq.index pattern q)) /\
             is_prefix_suffix #int pattern q j)
    (ensures j <= (if chars_match then k_final + 1 else 0))
  = if j = 0 then ()
    else begin
      Bridge.ps_decompose #int pattern q j;
      let jm1 = j - 1 in
      if jm1 > k_final then begin
        Bridge.apply_mismatch #int pattern q k_final jm1;
        assert False
      end else begin
        if chars_match then
          assert (j <= k_final + 1)
        else begin
          assert (jm1 <= k_final);
          assert (k_final == 0);
          assert (jm1 == 0);
          assert False
        end
      end
    end
#pop-options

/// Per-element non-negativity transfer (calls pi_max_instantiate_int internally)
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let nonneg_transfer_int (pattern pi_old pi_new: Seq.seq int)
    (q: nat{0 < q /\ q < Seq.length pattern})
    (r: nat{r < q + 1})
  : Lemma
    (requires pi_max_up_to_int pattern pi_old q /\
             Seq.length pi_old >= Seq.length pattern /\
             Seq.length pi_new >= Seq.length pattern /\
             (forall (s: nat). s < q ==> Seq.index pi_new s == Seq.index pi_old s) /\
             Seq.index pi_new q >= 0)
    (ensures Seq.index pi_new r >= 0)
  = if r < q then
      pi_max_instantiate_int pattern pi_old q r
    else ()
#pop-options

/// Per-element maximality transfer (TOP-LEVEL: isolated VC, no validity forall in scope)
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0 --split_queries always"
private let max_transfer_int (pattern pi_old pi_new: Seq.seq int)
    (q: nat{0 < q /\ q < Seq.length pattern})
    (k_final: nat) (chars_match: bool)
    (r: nat{r < q + 1}) (k: nat)
  : Lemma
    (requires pi_max_up_to_int pattern pi_old q /\
             Seq.length pi_old >= Seq.length pattern /\
             Seq.length pi_new >= Seq.length pattern /\
             (forall (s: nat). s < q ==> Seq.index pi_new s == Seq.index pi_old s) /\
             Seq.index pi_new q >= 0 /\
             Seq.index pi_new q == (if chars_match then k_final + 1 else k_final) /\
             is_prefix_suffix #int pattern (q - 1) k_final /\
             k_final < Seq.length pattern /\
             Bridge.all_ps_above_mismatch #int pattern q k_final /\
             (chars_match ==> Seq.index pattern k_final == Seq.index pattern q) /\
             (not chars_match ==> (k_final == 0 /\ Seq.index pattern k_final <> Seq.index pattern q)) /\
             is_prefix_suffix #int pattern r k)
    (ensures k <= Seq.index pi_new r)
  = if r < q then begin
      pi_max_max_at_int pattern pi_old q r k;
      assert (Seq.index pi_new r == Seq.index pi_old r)
    end else begin
      assert (r == q);
      maximality_at_q_int pattern q k_final chars_match k
    end
#pop-options

/// Main orchestrator: valid_aux is LOCAL (needs nonneg forall for subtyping),
/// max_transfer_int is TOP-LEVEL (isolated VC, no validity forall in scope).
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let extend_maximality_int pattern pi_old pi_new q k_final chars_match =
  assert (Seq.index pi_new q >= 0);
  establish_validity_at_q_int pattern pi_new q k_final chars_match;
  // Step 1: non-negativity forall
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires
      (nonneg_transfer_int pattern pi_old pi_new q));

  // Step 2: validity forall (LOCAL lambda — needs nonneg forall for subtyping)
  let valid_aux (r: nat{r < q + 1})
    : Lemma (is_prefix_suffix #int pattern r (Seq.index pi_new r))
    = if r < q then begin
        pi_max_instantiate_int pattern pi_old q r;
        assert (Seq.index pi_new r == Seq.index pi_old r)
      end else ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires valid_aux);

  // Step 3: maximality forall (TOP-LEVEL — no validity forall in its VC)
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2
      (max_transfer_int pattern pi_old pi_new q k_final chars_match));

  // Step 4: fold into opaque
  fold_pi_max_int pattern pi_new (q + 1)
#pop-options

let up_to_full_int pattern pi =
  reveal_opaque (`%pi_max_up_to_int) pi_max_up_to_int
