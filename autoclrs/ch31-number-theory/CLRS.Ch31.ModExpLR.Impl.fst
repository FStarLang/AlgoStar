(*
   Left-to-Right Modular Exponentiation — Pulse Implementation

   Implements the primary MODULAR-EXPONENTIATION from CLRS p. 957,
   scanning bits from MSB to LSB (left-to-right).

   The algorithm maintains d = b^c mod m where c is the prefix of the binary
   representation of e processed so far. At each step, we square d (doubling c)
   and optionally multiply by b (if the current bit is 1).

   Uses machine-width SZ.t types for clean C extraction via KaRaMeL.
   Bit extraction uses a concrete mask variable (power of 2) with SZ.t
   division and remainder, avoiding spec-level pow2 in extractable code.

   Functional correctness: result == mod_exp_spec b e m == pow b e % m
   Complexity bound: at most num_bits(e) squarings.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExpLR.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open FStar.Math.Lemmas
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.ModExpLR.Lemmas
open CLRS.Ch31.GCD.Complexity
open CLRS.Ch31.ModExpLR.Complexity
open CLRS.Common.Complexity

module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT

// ── Helper lemmas ────────────────────────────────────────────────

// Basic division algebra: e/d = 2*(e/(2*d)) + (e/d)%2 for d > 0
let lemma_bit_decompose_div (e: nat) (d: pos)
  : Lemma (e / d == 2 * (e / (op_Multiply 2 d)) + (e / d) % 2)
  = lemma_div_mod (e / d) 2;
    division_multiplication_lemma e d 2

// pow2(k) / 2 = pow2(k-1) for k > 0
let pow2_half (k: pos)
  : Lemma (pow2 k / 2 == pow2 (k - 1))
  = pow2_double_mult (k - 1)

// 2 * (pow2(k) / 2) = pow2(k) for k > 0
let pow2_even (k: pos)
  : Lemma (op_Multiply 2 (pow2 k / 2) == pow2 k)
  = pow2_half k

// num_bits(pow2(k)) = k + 1
let rec num_bits_pow2 (k: nat)
  : Lemma (ensures num_bits (pow2 k) == k + 1)
          (decreases k)
  = if k = 0 then ()
    else (
      pow2_double_mult (k - 1);
      assert (pow2 k / 2 == pow2 (k - 1));
      num_bits_pow2 (k - 1)
    )

// Mask loop: if pow2(k) <= n and pow2(k) > n/2, then k = num_bits(n) - 1
let rec mask_loop_done (n: pos) (k: nat)
  : Lemma (requires pow2 k <= n /\ pow2 k > n / 2)
          (ensures k == num_bits n - 1)
          (decreases n)
  = if n <= 1 then ()
    else if k = 0 then ()
    else (
      pow2_double_mult (k - 1);
      mask_loop_done (n / 2) (k - 1)
    )

// Mask loop: pow2(k) <= n implies k < num_bits(n)
let rec mask_loop_invariant_lemma (n: pos) (k: nat)
  : Lemma (requires pow2 k <= n)
          (ensures k < num_bits n)
          (decreases n)
  = if n <= 1 then ()
    else if k = 0 then ()
    else (
      pow2_double_mult (k - 1);
      mask_loop_invariant_lemma (n / 2) (k - 1)
    )

// b_mod preserves modular exponentiation step
#push-options "--z3rlimit 10"
let mod_exp_lr_step_bmod (b: int) (prefix: nat) (m: pos) (bit: nat{bit <= 1})
  : Lemma (
      let d = pow b prefix % m in
      let d_sq = (d * d) % m in
      let b_mod = b % m in
      let d_new = (if bit = 0 then d_sq else (d_sq * b_mod) % m) in
      d_new == pow b (2 * prefix + bit) % m
    )
  = let d = pow b prefix % m in
    let d_sq = (d * d) % m in
    mod_exp_lr_step b prefix m bit;
    if bit = 1 then
      lemma_mod_mul_distr_r d_sq b m
#pop-options

// After the step, d_new = pow b (e / mask) % m
// (since 2*(e/(2*mask)) + (e/mask)%2 = e/mask by division algebra)
let step_result_lemma (b: int) (e: nat) (mask: pos) (m: pos)
  : Lemma (
      let prefix = e / (op_Multiply 2 mask) in
      let bit = (e / mask) % 2 in
      let d = pow b prefix % m in
      let d_sq = (d * d) % m in
      let b_mod = b % m in
      let d_new = (if bit = 0 then d_sq else (d_sq * b_mod) % m) in
      d_new == pow b (e / mask) % m
    )
  = let prefix = e / (op_Multiply 2 mask) in
    let bit = (e / mask) % 2 in
    mod_exp_lr_step_bmod b prefix m bit;
    lemma_bit_decompose_div e mask;
    assert (e / mask == 2 * prefix + bit)

// ── Main function ────────────────────────────────────────────────

#push-options "--z3rlimit 10"
fn mod_exp_lr_impl (b_init e_init: SZ.t) (m_init: SZ.t{SZ.v m_init > 0 /\ SZ.fits (SZ.v m_init * SZ.v m_init)})
  (ctr: GR.ref nat) (#c0: erased nat)
  requires GR.pts_to ctr c0
  returns result: SZ.t
  ensures exists* (cf: nat). GR.pts_to ctr cf ** pure (
    mod_exp_spec (SZ.v b_init) (SZ.v e_init) (SZ.v m_init) == SZ.v result /\
    SZ.v result >= 0 /\ SZ.v result < SZ.v m_init /\
    modexp_lr_complexity_bounded cf (reveal c0) (SZ.v e_init)
  )
{
  lemma_prefix_zero (SZ.v e_init);

  if (e_init =^ 0sz) {
    // pow b 0 % m = 1 % m
    1sz %^ m_init
  } else {
    let b_mod = b_init %^ m_init;

    // Phase 1: Compute mask = pow2(num_bits(e) - 1) via doubling
    let mut mask : SZ.t = 1sz;
    let k_ref = GR.alloc #nat 0;
    while (
      let vm = !mask;
      vm <=^ (e_init /^ 2sz)
    )
    invariant exists* vm (kv: nat).
      R.pts_to mask vm **
      GR.pts_to k_ref kv **
      pure (
        SZ.v vm == pow2 kv /\
        pow2 kv <= SZ.v e_init /\
        kv < num_bits (SZ.v e_init)
      )
    decreases (SZ.v e_init - SZ.v !mask)
    {
      let vm = !mask;
      // vm <= e/2, so vm*2 <= e
      assert (pure (SZ.v vm * 2 <= SZ.v e_init));
      mask := vm *^ 2sz;
      // Ghost: update k
      with _vm kv. assert (R.pts_to mask (vm *^ 2sz) ** GR.pts_to k_ref kv);
      pow2_double_mult kv;
      mask_loop_invariant_lemma (SZ.v e_init) (kv + 1);
      GR.op_Colon_Equals k_ref (kv + 1);
    };

    // After mask loop: mask = pow2(k) with pow2(k) > e/2
    // Therefore k = num_bits(e) - 1
    let init_mask = !mask;
    with _vm kv_final. assert (R.pts_to mask init_mask ** GR.pts_to k_ref kv_final);
    mask_loop_done (SZ.v e_init) kv_final;
    num_bits_pow2 kv_final;

    // Phase 2: Main bit-processing loop
    let mut d : SZ.t = 1sz %^ m_init;

    // Update k_ref to track bits remaining
    GR.op_Colon_Equals k_ref kv_final;

    while (
      let vm = !mask;
      vm >^ 0sz
    )
    invariant exists* vd vmask (k: nat) (vc: nat).
      R.pts_to d vd **
      R.pts_to mask vmask **
      GR.pts_to k_ref k **
      GR.pts_to ctr vc **
      pure (
        SZ.v vd >= 0 /\ SZ.v vd < SZ.v m_init /\
        (SZ.v vmask > 0 ==>
          SZ.v vmask == pow2 k /\
          SZ.v vd == pow (SZ.v b_init) (SZ.v e_init / (op_Multiply 2 (SZ.v vmask))) % SZ.v m_init) /\
        (SZ.v vmask == 0 ==>
          mod_exp_spec (SZ.v b_init) (SZ.v e_init) (SZ.v m_init) == SZ.v vd) /\
        vc >= reveal c0 /\
        vc - reveal c0 + (if SZ.v vmask > 0 then k + 1 else 0) == num_bits (SZ.v e_init)
      )
    decreases (SZ.v !mask)
    {
      let vmask = !mask;
      let vd = !d;

      // Read ghost k for proofs
      with _vd _vmask kv _vc.
        assert (R.pts_to d vd ** R.pts_to mask vmask ** GR.pts_to k_ref kv ** GR.pts_to ctr _vc);

      // Concrete bit extraction
      let bit = (e_init /^ vmask) %^ 2sz;

      // Ghost proof: step correctness
      step_result_lemma (SZ.v b_init) (SZ.v e_init) (SZ.v vmask) (SZ.v m_init);

      // Prove multiplication fits in SZ.t
      assert (pure (SZ.v vd * SZ.v vd <= SZ.v vd * SZ.v m_init));
      assert (pure (SZ.v vd * SZ.v m_init < SZ.v m_init * SZ.v m_init));

      let sq = (vd *^ vd) %^ m_init;

      // Move tick/mask/k_update into each bit branch so d is concrete
      // (avoids match expression in d that Z3 can't reason about)
      if (bit =^ 1sz) {
        // bit = 1: d_new = (sq * b_mod) % m
        assert (pure (SZ.v sq * SZ.v b_mod <= SZ.v sq * SZ.v m_init));
        assert (pure (SZ.v sq * SZ.v m_init < SZ.v m_init * SZ.v m_init));
        d := (sq *^ b_mod) %^ m_init;

        tick ctr;
        mask := vmask /^ 2sz;

        if (vmask >^ 1sz) {
          pow2_half kv;
          pow2_even kv;
          GR.op_Colon_Equals k_ref (kv - 1);
        } else {
          GR.op_Colon_Equals k_ref 0;
        };
      } else {
        // bit = 0: d_new = sq
        d := sq;

        tick ctr;
        mask := vmask /^ 2sz;

        if (vmask >^ 1sz) {
          pow2_half kv;
          pow2_even kv;
          GR.op_Colon_Equals k_ref (kv - 1);
        } else {
          GR.op_Colon_Equals k_ref 0;
        };
      };
    };

    // After loop: mask = 0, d = pow(b, e) % m = mod_exp_spec b e m
    let r = !d;
    assert (pure (mod_exp_spec (SZ.v b_init) (SZ.v e_init) (SZ.v m_init) == SZ.v r));

    // Cleanup ghost k_ref
    with kf. assert (GR.pts_to k_ref kf);
    GR.free k_ref;

    r
  }
}
#pop-options
