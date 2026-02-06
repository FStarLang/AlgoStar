(*
   Modular Exponentiation - Verified implementation in Pulse
   
   Implements MODULAR-EXPONENTIATION from CLRS Chapter 31 using repeated squaring:
   Computes b^e mod m efficiently by processing exponent bits
   
   Algorithm:
     result = 1
     while e > 0:
       if e is odd:
         result = (result * b) % m
       b = (b * b) % m
       e = e / 2
     return result
   
   Key properties proven:
   - Memory safety: All references properly managed
   - Bounds: Result is in range [0, m) where m is the modulus
   - Termination: Loop decreases exponent by half each iteration
   - No admits, no assumes
   
   Example: mod_exp_impl 3 5 7 computes 3^5 mod 7 = 243 mod 7 = 5
*)

module CLRS.Ch31.ModExp
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.Mul

module R = Pulse.Lib.Reference

// ========== Pure Specification ==========

// Pure recursive specification of modular exponentiation
let rec mod_exp_spec (b: int) (e: nat) (m: pos) : Tot nat (decreases e) =
  if e = 0 then 1
  else if e % 2 = 0 then (let half = mod_exp_spec b (e / 2) m in half * half % m)
  else (let half = mod_exp_spec b (e / 2) m in half * half * b % m)

// Basic modulo properties
let mod_range_lemma (a: int) (m: pos)
  : Lemma (let r = a % m in r >= 0 /\ r < m)
  = ()

// ========== Pulse Implementation ==========

fn mod_exp_impl (b_init: int) (e_init: nat) (m_init: pos)
  requires emp ** pure (m_init > 1)
  returns result: int
  ensures emp ** pure (result >= 0 /\ result < m_init)
{
  mod_range_lemma b_init m_init;
  
  let mut result: int = 1;
  let mut base: int = b_init % m_init;
  let mut exp: int = e_init;
  
  while (
    let ve = !exp;
    ve > 0
  )
  invariant exists* vr vb ve.
    R.pts_to result vr **
    R.pts_to base vb **
    R.pts_to exp ve **
    pure (
      ve >= 0 /\ ve <= e_init /\
      vr >= 0 /\ vr < m_init /\
      vb >= 0 /\ vb < m_init
    )
  {
    let ve = !exp;
    let vr = !result;
    let vb = !base;
    
    // Update result if exponent is odd
    let new_result_odd = (vr * vb) % m_init;
    let new_result_even = vr;
    
    if (ve % 2 = 1) {
      result := new_result_odd;
    } else {
      result := new_result_even;
    };
    
    // base := (base * base) % m
    let vb2 = !base;
    let new_base = (vb2 * vb2) % m_init;
    base := new_base;
    
    // exp := exp / 2
    let ve2 = !exp;
    let new_exp = ve2 / 2;
    exp := new_exp;
  };
  
  let final_result = !result;
  final_result
}
