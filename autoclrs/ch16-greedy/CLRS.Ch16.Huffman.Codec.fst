(*
   Huffman Encode / Decode — Codec

   Encode and decode using Huffman prefix codes, with verified round-trip:
     decode(encode(msg)) == msg
     encode(decode(bits)) == bits  (for well-formed trees)

   Built directly on the htree type from CLRS.Ch16.Huffman.Spec.
   Leaves carry symbol indices (sym:nat) per CLRS §16.3.

   Convention: true = go left, false = go right (matches tree_position in Spec).

   NO admits. NO assumes.
*)
module CLRS.Ch16.Huffman.Codec

open FStar.List.Tot
open FStar.List.Tot.Properties
open CLRS.Ch16.Huffman.Spec

(*** Symbol collection and well-formedness ***)

// symbols, no_dup, wf_htree, sym_in_tree defined in .fsti

(*** Codeword: path from root to a symbol's leaf ***)

// Find the codeword (bit path) for a symbol.
// Returns None if the symbol is not in the tree.
let rec codeword (t: htree) (s: nat) : option (list bool) =
  match t with
  | Leaf s' _ -> if s = s' then Some [] else None
  | Internal _ l r ->
    match codeword l s with
    | Some path -> Some (true :: path)
    | None ->
      match codeword r s with
      | Some path -> Some (false :: path)
      | None -> None

(*** Encode: message (list of symbol indices) -> bitstring ***)

let rec encode (t: htree) (msg: list nat) : option (list bool) =
  match msg with
  | [] -> Some []
  | s :: rest ->
    match codeword t s, encode t rest with
    | Some cw, Some rest_bits -> Some (cw @ rest_bits)
    | _, _ -> None

(*** Decode: bitstring -> message ***)

// Decode one symbol by walking from the current node.
// Returns (symbol, remaining bits) or None.
let rec decode_step (cur: htree) (bits: list bool) : option (nat & list bool) =
  match cur with
  | Leaf s _ -> Some (s, bits)
  | Internal _ l r ->
    match bits with
    | [] -> None
    | b :: rest ->
      if b then decode_step l rest
      else decode_step r rest

// Decode a full bitstring by repeatedly walking from the root.
let rec decode (t: htree) (bits: list bool) : Tot (option (list nat))
  (decreases length bits) =
  match bits with
  | [] -> Some []
  | _ ->
    match decode_step t bits with
    | None -> None
    | Some (s, remaining) ->
      if length remaining < length bits then
        match decode t remaining with
        | Some rest_msg -> Some (s :: rest_msg)
        | None -> None
      else None

(*** Computation rules — must match .fsti declaration order ***)

let decode_step_leaf (s: nat) (f: pos) (bits: list bool)
  : Lemma (decode_step (Leaf s f) bits == Some (s, bits))
  = ()

let decode_step_internal (f: pos) (l r: htree) (b: bool) (rest: list bool)
  : Lemma (decode_step (Internal f l r) (b :: rest) ==
            (if b then decode_step l rest else decode_step r rest))
  = ()

let decode_step_internal_nil (f: pos) (l r: htree)
  : Lemma (decode_step (Internal f l r) [] == None)
  = ()

let rec decode_step_progress (cur: htree) (bits: list bool)
  : Lemma (requires Internal? cur /\ Some? (decode_step cur bits))
          (ensures (let ds = Some?.v (decode_step cur bits) in
                    length (snd ds) < length bits))
          (decreases cur)
  = match cur with
    | Internal _ l r ->
      let b :: rest = bits in
      let child = if b then l else r in
      match child with
      | Leaf _ _ -> ()
      | Internal _ _ _ -> decode_step_progress child rest

let decode_nil (t: htree) : Lemma (decode t [] == Some []) = ()

let decode_cons (t: htree) (bits: list bool)
  : Lemma (requires Cons? bits /\ Internal? t /\ Some? (decode_step t bits))
          (ensures (let ds = Some?.v (decode_step t bits) in
                    length (snd ds) < length bits /\
                    (match decode t (snd ds) with
                     | Some rest_msg -> decode t bits == Some (fst ds :: rest_msg)
                     | None -> decode t bits == None)))
  = decode_step_progress t bits

let decode_some_implies_step (t: htree) (bits: list bool)
  : Lemma (requires Internal? t /\ Cons? bits /\ Some? (decode t bits))
          (ensures Some? (decode_step t bits))
  = ()

let list_index_zero (#a: Type) (hd: a) (tl: list a)
  : Lemma (index (hd :: tl) 0 == hd) = ()

let list_index_succ (#a: Type) (hd: a) (tl: list a) (i: nat{i < length tl})
  : Lemma (index (hd :: tl) (i + 1) == index tl i) = ()

let codeword_leaf_match (s: nat) (f: pos) : Lemma (codeword (Leaf s f) s == Some []) = ()

let codeword_leaf_mismatch (s s': nat) (f: pos)
  : Lemma (requires s <> s') (ensures codeword (Leaf s' f) s == None) = ()

let codeword_internal (f: pos) (l r: htree) (s: nat)
  : Lemma (codeword (Internal f l r) s ==
           (match codeword l s with
            | Some path -> Some (true :: path)
            | None -> match codeword r s with
                      | Some path -> Some (false :: path)
                      | None -> None))
  = ()

let encode_nil (t: htree) : Lemma (encode t [] == Some []) = ()

let encode_cons (t: htree) (s: nat) (rest: list nat)
  : Lemma (encode t (s :: rest) ==
           (match codeword t s, encode t rest with
            | Some cw, Some rest_bits -> Some (cw @ rest_bits)
            | _, _ -> None))
  = ()

(*** Helper lemmas ***)

// codeword is non-empty for symbols in an Internal tree
let codeword_nonempty (t: htree) (s: nat)
  : Lemma (requires Internal? t /\ Some? (codeword t s))
          (ensures (let Some cw = codeword t s in Cons? cw))
  = ()

// decode_step of a codeword yields the symbol and remaining bits
let rec decode_step_codeword (t: htree) (s: nat) (rest: list bool)
  : Lemma (requires Some? (codeword t s))
          (ensures (let Some cw = codeword t s in
                    decode_step t (cw @ rest) == Some (s, rest)))
          (decreases t)
  = match t with
    | Leaf s' _ -> ()
    | Internal _ l r ->
      match codeword l s with
      | Some _ -> decode_step_codeword l s rest
      | None ->
        match codeword r s with
        | Some _ -> decode_step_codeword r s rest
        | None -> ()

(*** Main theorem: encode then decode = identity ***)

let rec encode_decode_roundtrip (t: htree) (msg: list nat)
  : Lemma (requires Internal? t /\ Some? (encode t msg))
          (ensures (let Some bits = encode t msg in
                    decode t bits == Some msg))
          (decreases msg)
  = match msg with
    | [] -> ()
    | s :: rest ->
      let Some cw = codeword t s in
      let Some rest_bits = encode t rest in
      decode_step_codeword t s rest_bits;
      codeword_nonempty t s;
      append_length cw rest_bits;
      encode_decode_roundtrip t rest

(*** Converse: decode then encode = identity ***)

// codeword returns None for symbols not in the tree
let rec codeword_none_if_absent (t: htree) (s: nat)
  : Lemma (requires not (sym_in_tree s t))
          (ensures codeword t s == None)
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ l r ->
      append_mem (symbols l) (symbols r) s;
      codeword_none_if_absent l s;
      codeword_none_if_absent r s

// decode_step produces a symbol present in the tree
let rec decode_step_sym_in_tree (t: htree) (bits: list bool)
  : Lemma (requires Some? (decode_step t bits))
          (ensures (let Some (s, _) = decode_step t bits in sym_in_tree s t))
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ l r ->
      let b :: rest = bits in
      let child = if b then l else r in
      match child with
      | Leaf s _ -> append_mem (symbols l) (symbols r) s
      | Internal _ _ _ ->
        decode_step_sym_in_tree child rest;
        let Some (s, _) = decode_step child rest in
        append_mem (symbols l) (symbols r) s

// no_dup helpers
let rec no_dup_append_left (l1 l2: list nat)
  : Lemma (requires no_dup (l1 @ l2)) (ensures no_dup l1) (decreases l1)
  = match l1 with
    | [] -> ()
    | hd :: tl -> append_mem tl l2 hd; no_dup_append_left tl l2

let rec no_dup_append_right (l1 l2: list nat)
  : Lemma (requires no_dup (l1 @ l2)) (ensures no_dup l2) (decreases l1)
  = match l1 with
    | [] -> ()
    | _ :: tl -> no_dup_append_right tl l2

let rec no_dup_append_disjoint (l1 l2: list nat) (x: nat)
  : Lemma (requires no_dup (l1 @ l2) /\ mem x l2) (ensures not (mem x l1))
          (decreases l1)
  = match l1 with
    | [] -> ()
    | _ :: tl -> append_mem tl l2 (hd l1); no_dup_append_disjoint tl l2 x

let wf_internal_left (t: htree{Internal? t /\ wf_htree t})
  : Lemma (let Internal _ l _ = t in wf_htree l)
  = let Internal _ l r = t in no_dup_append_left (symbols l) (symbols r)

let wf_internal_right (t: htree{Internal? t /\ wf_htree t})
  : Lemma (let Internal _ _ r = t in wf_htree r)
  = let Internal _ l r = t in no_dup_append_right (symbols l) (symbols r)

// Inverse: decode_step decomposes bits into codeword @ remaining
let rec decode_step_inv (t: htree) (bits: list bool)
  : Lemma (requires wf_htree t /\ Some? (decode_step t bits))
          (ensures (let Some (s, remaining) = decode_step t bits in
                    Some? (codeword t s) /\
                    (let Some cw = codeword t s in bits == cw @ remaining)))
          (decreases t)
  = match t with
    | Leaf _ _ -> ()
    | Internal _ l r ->
      let b :: rest = bits in
      if b then (
        wf_internal_left t;
        decode_step_inv l rest
      ) else (
        wf_internal_right t;
        decode_step_inv r rest;
        let Some (s, _) = decode_step r rest in
        decode_step_sym_in_tree r rest;
        no_dup_append_disjoint (symbols l) (symbols r) s;
        codeword_none_if_absent l s
      )

let rec decode_encode_roundtrip (t: htree) (bits: list bool)
  : Lemma (requires Internal? t /\ wf_htree t /\ Some? (decode t bits))
          (ensures (let Some msg = decode t bits in
                    Some? (encode t msg) /\
                    (let Some bits' = encode t msg in bits == bits')))
          (decreases length bits)
  = match bits with
    | [] -> ()
    | _ ->
      decode_step_progress t bits;
      decode_step_inv t bits;
      let Some (_, remaining) = decode_step t bits in
      if length remaining > 0 then
        decode_encode_roundtrip t remaining
