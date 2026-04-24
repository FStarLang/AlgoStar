(*
   Strassen's Matrix Multiplication Algorithm (CLRS §4.2, pp. 79–82) — Specification
   
   Pure functional definitions: matrix type, operations, standard multiply,
   submatrix extraction, and the Strassen algorithm itself.
*)

module CLRS.Ch04.Strassen.Spec
open FStar.Seq
open FStar.Math.Lemmas
open FStar.Classical

module Seq = FStar.Seq

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

// ========== Matrix Representation ==========

//SNIPPET_START: matrix_type
// Matrix as sequence of sequences (rows)
type matrix = s:Seq.seq (Seq.seq int){
  Seq.length s > 0 /\
  Seq.length (Seq.index s 0) > 0 /\
  (forall (i:nat). i < Seq.length s ==> 
    Seq.length (Seq.index s i) == Seq.length (Seq.index s 0))
}

let rows (m:matrix) : pos = Seq.length m
let cols (m:matrix) : pos = 
  let c = Seq.length (Seq.index m 0) in
  assert (c > 0);
  c

let is_square (m:matrix) : prop = rows m == cols m

let get_elem (m:matrix) (i:nat{i < rows m}) (j:nat{j < cols m}) : int =
  Seq.index (Seq.index m i) j
//SNIPPET_END: matrix_type

// ========== Power of 2 predicate ==========

let rec is_pow2 (n:pos) : bool =
  if n = 1 then true
  else if n % 2 = 1 then false
  else is_pow2 (n / 2)

let pow2_size (m:matrix{is_square m}) : prop =
  is_pow2 (rows m)

// Helper lemmas about power of 2
let lemma_pow2_half (n:pos{is_pow2 n /\ n > 1})
  : Lemma (ensures is_pow2 (n / 2) /\ n / 2 > 0)
  = ()

let lemma_pow2_double (n:pos{is_pow2 n})
  : Lemma (ensures 2 * n > 0 /\ is_pow2 (2 * n))
  = ()

// Lemma: submatrices that are square and power-of-2 retain that property
let lemma_submatrix_pow2 (m:matrix{is_square m /\ pow2_size m})
                         (k:nat{k > 0 /\ 2 * k == rows m})
  : Lemma (let half = rows m / 2 in
           half == k /\
           is_pow2 half)
  = lemma_pow2_half (rows m)

// ========== Matrix Addition/Subtraction ==========

let matrix_add (a b:matrix{rows a == rows b /\ cols a == cols b}) 
  : m:matrix{rows m == rows a /\ cols m == cols a /\ (is_square a ==> is_square m)} 
  = let n = rows a in
    let m = cols a in
    Seq.init n (fun i ->
      Seq.init m (fun j ->
        get_elem a i j + get_elem b i j))

let matrix_sub (a b:matrix{rows a == rows b /\ cols a == cols b}) 
  : m:matrix{rows m == rows a /\ cols m == cols a /\ (is_square a ==> is_square m)}
  = let n = rows a in
    let m = cols a in
    Seq.init n (fun i ->
      Seq.init m (fun j ->
        get_elem a i j - get_elem b i j))

// ========== Standard Matrix Multiplication (Specification) ==========

//SNIPPET_START: standard_multiply
// Dot product of row i of a and column j of b
// Note: this operates on seq-of-seq matrices. See also:
// CLRS.Ch04.MatrixMultiply.dot_product_spec which defines the equivalent
// sum over flat (row-major) arrays.
let rec dot_product (a b:matrix) (i:nat{i < rows a}) (j:nat{j < cols b})
                    (k:nat{k <= cols a /\ k <= rows b})
  : Tot int (decreases k)
  = if k = 0 then 0
    else dot_product a b i j (k-1) + get_elem a i (k-1) * get_elem b (k-1) j

let standard_multiply (a b:matrix{cols a == rows b}) 
  : m:matrix{rows m == rows a /\ cols m == cols b}
  = let n = rows a in
    let m = cols b in
    let p = cols a in  // = rows b
    Seq.init n (fun i ->
      Seq.init m (fun j ->
        dot_product a b i j p))
//SNIPPET_END: standard_multiply

// ========== Submatrix Extraction ==========

// Extract submatrix [row_start..row_end) × [col_start..col_end)
let submatrix (m:matrix)
              (row_start:nat) (row_end:nat{row_start < row_end /\ row_end <= rows m})
              (col_start:nat) (col_end:nat{col_start < col_end /\ col_end <= cols m})
  : sub:matrix{rows sub == row_end - row_start /\ cols sub == col_end - col_start}
  = let sub_rows = row_end - row_start in
    let sub_cols = col_end - col_start in
    Seq.init sub_rows (fun i ->
      Seq.init sub_cols (fun j ->
        get_elem m (row_start + i) (col_start + j)))

// ========== Matrix Assembly from Quadrants ==========

// Assemble 4 quadrants into a single matrix (all quadrants same size n×n)
let assemble_quadrants (c11 c12 c21 c22:matrix)
  : Pure matrix
    (requires 
      rows c11 == rows c12 /\ 
      rows c11 == rows c21 /\ 
      rows c11 == rows c22 /\
      cols c11 == cols c12 /\ 
      cols c11 == cols c21 /\ 
      cols c11 == cols c22 /\
      rows c11 == cols c11)  // square
    (ensures fun m -> 
      rows m == 2 * rows c11 /\
      cols m == 2 * cols c11)
  = let n = rows c11 in
    let full_n = 2 * n in
    Seq.init full_n (fun (i:nat{i < full_n}) ->
      Seq.init full_n (fun (j:nat{j < full_n}) ->
        if i < n then
          if j < n then get_elem c11 i j
          else (
            let j' = j - n in
            assert (j' < n);
            get_elem c12 i j'
          )
        else (
          let i' = i - n in
          assert (i' < n);
          if j < n then get_elem c21 i' j
          else (
            let j' = j - n in
            assert (j' < n);
            get_elem c22 i' j'
          )
        )))

// ========== Strassen's Algorithm ==========

#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"

//SNIPPET_START: strassen_multiply
let rec strassen_multiply (a b:matrix{cols a == rows b /\ is_square a /\ is_square b /\ pow2_size a})
  : Tot (m:matrix{rows m == rows a /\ cols m == cols b /\ is_square m}) (decreases rows a)
//SNIPPET_END: strassen_multiply
  = let n = rows a in
    if n = 1 then
      // Base case: 1×1 matrix, use standard multiply
      standard_multiply a b
    else
      // Divide into quadrants
      let half = n / 2 in
      lemma_pow2_half n;
      
      let a11 = submatrix a 0 half 0 half in
      let a12 = submatrix a 0 half half n in
      let a21 = submatrix a half n 0 half in
      let a22 = submatrix a half n half n in
      
      let b11 = submatrix b 0 half 0 half in
      let b12 = submatrix b 0 half half n in
      let b21 = submatrix b half n 0 half in
      let b22 = submatrix b half n half n in
      
//SNIPPET_START: strassen_products
      // Compute the 7 products (P1..P7) using Strassen's formulas
      // P1 = A11 * (B12 - B22)
      let p1 = strassen_multiply a11 (matrix_sub b12 b22) in
      // P2 = (A11 + A12) * B22
      let p2 = strassen_multiply (matrix_add a11 a12) b22 in
      // P3 = (A21 + A22) * B11
      let p3 = strassen_multiply (matrix_add a21 a22) b11 in
      // P4 = A22 * (B21 - B11)
      let p4 = strassen_multiply a22 (matrix_sub b21 b11) in
      // P5 = (A11 + A22) * (B11 + B22)
      let p5 = strassen_multiply (matrix_add a11 a22) (matrix_add b11 b22) in
      // P6 = (A12 - A22) * (B21 + B22)
      let p6 = strassen_multiply (matrix_sub a12 a22) (matrix_add b21 b22) in
      // P7 = (A11 - A21) * (B11 + B12)
      let p7 = strassen_multiply (matrix_sub a11 a21) (matrix_add b11 b12) in
      //SNIPPET_END: strassen_products
      
      // All products should be half × half
      assert (rows p1 == half /\ cols p1 == half);
      assert (rows p2 == half /\ cols p2 == half);
      assert (rows p3 == half /\ cols p3 == half);
      assert (rows p4 == half /\ cols p4 == half);
      assert (rows p5 == half /\ cols p5 == half);
      assert (rows p6 == half /\ cols p6 == half);
      assert (rows p7 == half /\ cols p7 == half);
      
//SNIPPET_START: strassen_combine
      // Combine into result quadrants using Strassen's formulas
      // C11 = P5 + P4 - P2 + P6
      let c11 = matrix_add (matrix_sub (matrix_add p5 p4) p2) p6 in
      // C12 = P1 + P2
      let c12 = matrix_add p1 p2 in
      // C21 = P3 + P4
      let c21 = matrix_add p3 p4 in
      // C22 = P5 + P1 - P3 - P7
      let c22 = matrix_sub (matrix_sub (matrix_add p5 p1) p3) p7 in
      //SNIPPET_END: strassen_combine
      
      // Result quadrants are all half × half
      assert (rows c11 == half /\ cols c11 == half);
      assert (rows c12 == half /\ cols c12 == half);
      assert (rows c21 == half /\ cols c21 == half);
      assert (rows c22 == half /\ cols c22 == half);
      
      let result = assemble_quadrants c11 c12 c21 c22 in
      assert (rows result == 2 * half);
      assert (cols result == 2 * half);
      assert (rows result == n);
      result

#pop-options

#pop-options
