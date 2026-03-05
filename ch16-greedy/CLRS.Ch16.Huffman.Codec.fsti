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

// decode_step rules
val decode_step_leaf (s: nat) (f: pos) (bits: list bool)
  : Lemma (decode_step (Leaf s f) bits == Some (s, bits))

val decode_step_internal (f: pos) (l r: htree) (b: bool) (rest: list bool)
  : Lemma (decode_step (Internal f l r) (b :: rest) ==
            (if b then decode_step l rest else decode_step r rest))

val decode_step_internal_nil (f: pos) (l r: htree)
  : Lemma (decode_step (Internal f l r) [] == None)

/// decode_step on Internal always consumes at least one bit
val decode_step_progress (cur: htree) (bits: list bool)
  : Lemma (requires Internal? cur /\ Some? (decode_step cur bits))
          (ensures (let ds = Some?.v (decode_step cur bits) in
                    length (snd ds) < length bits))

// decode rules
val decode_nil (t: htree)
  : Lemma (decode t [] == Some [])

val decode_cons (t: htree) (bits: list bool)
  : Lemma (requires Cons? bits /\ Internal? t /\ Some? (decode_step t bits))
          (ensures (let ds = Some?.v (decode_step t bits) in
                    length (snd ds) < length bits /\
                    (match decode t (snd ds) with
                     | Some rest_msg -> decode t bits == Some (fst ds :: rest_msg)
                     | None -> decode t bits == None)))

/// If decode succeeds on non-empty bits, then decode_step also succeeds
val decode_some_implies_step (t: htree) (bits: list bool)
  : Lemma (requires Internal? t /\ Cons? bits /\ Some? (decode t bits))
          (ensures Some? (decode_step t bits))

/// List indexing into cons
val list_index_zero (#a: Type) (hd: a) (tl: list a)
  : Lemma (index (hd :: tl) 0 == hd)

val list_index_succ (#a: Type) (hd: a) (tl: list a) (i: nat{i < length tl})
  : Lemma (index (hd :: tl) (i + 1) == index tl i)

// codeword rules
val codeword_leaf_match (s: nat) (f: pos)
  : Lemma (codeword (Leaf s f) s == Some [])

val codeword_leaf_mismatch (s s': nat) (f: pos)
  : Lemma (requires s <> s')
          (ensures codeword (Leaf s' f) s == None)

val codeword_internal (f: pos) (l r: htree) (s: nat)
  : Lemma (codeword (Internal f l r) s ==
           (match codeword l s with
            | Some path -> Some (true :: path)
            | None -> match codeword r s with
                      | Some path -> Some (false :: path)
                      | None -> None))

// encode rules
val encode_nil (t: htree)
  : Lemma (encode t [] == Some [])

val encode_cons (t: htree) (s: nat) (rest: list nat)
  : Lemma (encode t (s :: rest) ==
           (match codeword t s, encode t rest with
            | Some cw, Some rest_bits -> Some (cw @ rest_bits)
            | _, _ -> None))

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
