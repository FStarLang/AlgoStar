(*
   Strassen's Algorithm — Correctness Proofs (CLRS §4.2)
   
   Interface for correctness lemmas proving Strassen equals standard multiply.
*)

module CLRS.Ch04.Strassen.Lemmas

open FStar.Mul
open FStar.Seq
open FStar.Math.Lemmas
open FStar.Classical
open CLRS.Ch04.Strassen.Spec

module Seq = FStar.Seq

// Auxiliary sum for dot product split proofs
val dot_product_aux (a b:matrix{cols a == rows b})
                    (i:nat{i < rows a}) (j:nat{j < cols b})
                    (k1 k2:nat{k1 <= k2 /\ k2 <= cols a})
  : Tot int (decreases (k2 - k1))

val lemma_dot_product_split (a b:matrix{cols a == rows b})
                            (i:nat{i < rows a}) (j:nat{j < cols b})
                            (k1 k2:nat{k1 <= k2 /\ k2 <= cols a})
  : Lemma (ensures dot_product a b i j k2 == 
                   dot_product a b i j k1 + dot_product_aux a b i j k1 k2)

val lemma_standard_multiply_correct (a b:matrix{cols a == rows b}) (i:nat{i < rows a}) (j:nat{j < cols b})
  : Lemma (ensures get_elem (standard_multiply a b) i j == dot_product a b i j (cols a))

val lemma_submatrix_elem (m:matrix)
                         (row_start:nat) (row_end:nat{row_start < row_end /\ row_end <= rows m})
                         (col_start:nat) (col_end:nat{col_start < col_end /\ col_end <= cols m})
                         (i:nat{i < row_end - row_start}) (j:nat{j < col_end - col_start})
  : Lemma (ensures get_elem (submatrix m row_start row_end col_start col_end) i j ==
                   get_elem m (row_start + i) (col_start + j))

val lemma_matrix_add_elem (a b:matrix{rows a == rows b /\ cols a == cols b})
                          (i:nat{i < rows a}) (j:nat{j < cols a})
  : Lemma (ensures get_elem (matrix_add a b) i j == get_elem a i j + get_elem b i j)

val lemma_matrix_sub_elem (a b:matrix{rows a == rows b /\ cols a == cols b})
                          (i:nat{i < rows a}) (j:nat{j < cols a})
  : Lemma (ensures get_elem (matrix_sub a b) i j == get_elem a i j - get_elem b i j)

val lemma_submatrix_square_pow2
  (m:matrix{is_square m /\ pow2_size m /\ rows m > 1})
  : Lemma (let n = rows m in
           let half = n / 2 in
           half > 0 /\
           is_pow2 half /\
           n - half == half)

// Element-wise correctness
val lemma_strassen_elem_correct 
  (a b:matrix{cols a == rows b /\ is_square a /\ is_square b /\ pow2_size a})
  (i:nat{i < rows a}) (j:nat{j < cols b})
  : Lemma (ensures get_elem (strassen_multiply a b) i j == get_elem (standard_multiply a b) i j)

//SNIPPET_START: strassen_correct
val lemma_strassen_correct (a b:matrix{cols a == rows b /\ is_square a /\ is_square b /\ pow2_size a})
  : Lemma (ensures (forall (i:nat) (j:nat). i < rows a /\ j < cols b ==>
                    get_elem (strassen_multiply a b) i j == get_elem (standard_multiply a b) i j))
//SNIPPET_END: strassen_correct
