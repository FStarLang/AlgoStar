(*
   Huffman Encode / Decode — Public Interface

   Verified round-trip encode/decode for Huffman prefix codes.
   Built on the htree type from CLRS.Ch16.Huffman.Spec (leaves carry sym:nat).

   NO admits. NO assumes.
*)
module CLRS.Ch16.Huffman.Codec

open FStar.List.Tot
open FStar.List.Tot.Properties
open CLRS.Ch16.Huffman.Spec

(*** Symbols and well-formedness ***)

let rec symbols (t: htree) : list nat =
  match t with
  | Leaf s _ -> [s]
  | Internal _ l r -> symbols l @ symbols r

let rec no_dup (l: list nat) : bool =
  match l with
  | [] -> true
  | hd :: tl -> not (mem hd tl) && no_dup tl

let wf_htree (t: htree) : bool = no_dup (symbols t)

let sym_in_tree (s: nat) (t: htree) : bool = mem s (symbols t)

(*** Core operations ***)

val codeword (t: htree) (s: nat) : option (list bool)

val encode (t: htree) (msg: list nat) : option (list bool)

val decode_step (cur: htree) (bits: list bool) : option (nat & list bool)

val decode (t: htree) (bits: list bool) : Tot (option (list nat))

(*** Computation rules (for use by Codec.Impl) ***)

val decode_step_leaf (s: nat) (f: pos) (bits: list bool)
  : Lemma (decode_step (Leaf s f) bits == Some (s, bits))

val decode_step_internal (f: pos) (l r: htree) (b: bool) (rest: list bool)
  : Lemma (decode_step (Internal f l r) (b :: rest) ==
            (if b then decode_step l rest else decode_step r rest))

val decode_step_internal_nil (f: pos) (l r: htree)
  : Lemma (decode_step (Internal f l r) [] == None)

(*** Round-trip theorems ***)

/// encode then decode = identity (no wf needed — prefix-free is structural)
val encode_decode_roundtrip (t: htree) (msg: list nat)
  : Lemma (requires Internal? t /\ Some? (encode t msg))
          (ensures (let Some bits = encode t msg in
                    decode t bits == Some msg))

/// decode then encode = identity (needs well-formedness for uniqueness)
val decode_encode_roundtrip (t: htree) (bits: list bool)
  : Lemma (requires Internal? t /\ wf_htree t /\ Some? (decode t bits))
          (ensures (let Some msg = decode t bits in
                    Some? (encode t msg) /\
                    (let Some bits' = encode t msg in bits == bits')))
