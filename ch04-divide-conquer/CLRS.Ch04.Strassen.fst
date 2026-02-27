(*
   Strassen's Matrix Multiplication Algorithm (CLRS §4.2, pp. 79–82)
   
   Implements Strassen's divide-and-conquer algorithm for n×n matrix
   multiplication where n is a power of 2.
   
   Standard algorithm: T(n) = 8T(n/2) + Θ(n²) → O(n³)
   Strassen's insight: compute 7 products (P1..P7) instead of 8
                      T(n) = 7T(n/2) + Θ(n²) → O(n^{lg 7}) ≈ O(n^{2.807})
   
   Divide matrices A,B into quadrants:
     A = [A11 A12]    B = [B11 B12]
         [A21 A22]        [B21 B22]
   
   Compute 7 products:
     P1 = A11 * (B12 - B22)
     P2 = (A11 + A12) * B22
     P3 = (A21 + A22) * B11
     P4 = A22 * (B21 - B11)
     P5 = (A11 + A22) * (B11 + B22)
     P6 = (A12 - A22) * (B21 + B22)
     P7 = (A11 - A21) * (B11 + B12)
   
   Result:
     C11 = P5 + P4 - P2 + P6
     C12 = P1 + P2
     C21 = P3 + P4
     C22 = P5 + P1 - P3 - P7
   
   This file proves:
   1. Functional correctness: Strassen equals standard matrix multiply
   2. Complexity: O(n^{lg 7}) scalar multiplications (closed form: 7^{log₂ n})
   
   All properties are fully proven, including the structural property that
   submatrix quadrants preserve square/pow2 (via lemma_submatrix_square_pow2).
*)

module CLRS.Ch04.Strassen
open FStar.Mul
open FStar.Seq
open FStar.Math.Lemmas
open FStar.Classical

module Seq = FStar.Seq

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"

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

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"

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

// ========== Complexity Analysis ==========

// Helper for log2
let rec log2_floor (n:pos) : Tot nat (decreases n) =
  if n = 1 then 0
  else 1 + log2_floor (n / 2)

// Power of 7 function (7^n)
let rec pow7 (n:nat) : Tot pos (decreases n) =
  if n = 0 then 1
  else 7 * pow7 (n - 1)

//SNIPPET_START: strassen_complexity
// Number of matrix multiplications performed by Strassen
let rec strassen_mult_count (n:pos{is_pow2 n}) : Tot nat (decreases n) =
  if n = 1 then 1
  else 7 * strassen_mult_count (n / 2)

// Standard matrix multiply: n³ multiplications
let standard_mult_count (n:pos) : nat = n * n * n

// Strassen performs fewer multiplications than standard
let rec lemma_strassen_better_than_cubic (n:pos{is_pow2 n /\ n > 1})
  : Lemma (ensures strassen_mult_count n < standard_mult_count n)
          (decreases n)
  = if n = 2 then ()
    else lemma_strassen_better_than_cubic (n / 2)
//SNIPPET_END: strassen_complexity

// T(n) = 7T(n/2) for multiplications
// Solving: T(n) = 7^{log_2 n} = n^{log_2 7} ≈ n^{2.807}
// Master theorem: a=7, b=2, f(n)=0, so T(n) = Θ(n^{log_b a}) = Θ(n^{log_2 7})

// Lemma 1: For powers of 2, pow2(log2_floor(n)) equals n
let rec lemma_pow2_log2_inverse (n:pos{is_pow2 n})
  : Lemma (ensures pow2 (log2_floor n) == n)
          (decreases n)
  = if n = 1 then ()
    else begin
      lemma_pow2_half n;
      lemma_pow2_log2_inverse (n / 2);
      pow2_double_mult (log2_floor (n / 2))
    end

// Lemma 2: log2_floor relates to division by 2
let lemma_log2_half (n:pos{is_pow2 n /\ n > 1})
  : Lemma (ensures log2_floor n == 1 + log2_floor (n / 2))
  = ()

// Lemma 3: pow7 relates to multiplication by 7
let lemma_pow7_succ (k:nat)
  : Lemma (ensures pow7 (k + 1) == 7 * pow7 k)
  = ()

//SNIPPET_START: strassen_closed_form
// Prove the closed form
let rec lemma_strassen_mult_closed_form (n:pos{is_pow2 n})
  : Lemma (ensures (let k = log2_floor n in
                    strassen_mult_count n == pow7 k))
          (decreases n)
  = if n = 1 then ()
    else begin
      let half = n / 2 in
      lemma_pow2_half n;
      lemma_strassen_mult_closed_form half;
      lemma_log2_half n;
      lemma_pow7_succ (log2_floor half)
    end
//SNIPPET_END: strassen_closed_form

// ========== Correctness Proof ==========

// Helper: auxiliary sum function for dot product
let rec dot_product_aux (a b:matrix{cols a == rows b})
                        (i:nat{i < rows a}) (j:nat{j < cols b})
                        (k1 k2:nat{k1 <= k2 /\ k2 <= cols a})
  : Tot int (decreases (k2 - k1))
  = if k1 = k2 then 0
    else get_elem a i k1 * get_elem b k1 j + dot_product_aux a b i j (k1 + 1) k2

// Helper: properties of dot product - split at intermediate point
let rec lemma_dot_product_split (a b:matrix{cols a == rows b})
                                (i:nat{i < rows a}) (j:nat{j < cols b})
                                (k1 k2:nat{k1 <= k2 /\ k2 <= cols a})
  : Lemma (ensures dot_product a b i j k2 == 
                   dot_product a b i j k1 + dot_product_aux a b i j k1 k2)
          (decreases k2)
  = if k2 = 0 then ()
    else if k1 = k2 then ()
    else begin
      // Use induction on k2
      lemma_dot_product_split a b i j k1 (k2 - 1);
      // dot_product a b i j k2 = dot_product a b i j (k2-1) + a[i,k2-1] * b[k2-1,j]
      // By IH: dot_product a b i j (k2-1) = dot_product a b i j k1 + dot_product_aux a b i j k1 (k2-1)
      // Need to show: dot_product_aux a b i j k1 k2 = dot_product_aux a b i j k1 (k2-1) + a[i,k2-1] * b[k2-1,j]
      // This follows by induction on k1
      let rec aux_split (k:nat{k <= k2 - 1})
        : Lemma (ensures dot_product_aux a b i j k k2 == 
                         dot_product_aux a b i j k (k2 - 1) + 
                         get_elem a i (k2 - 1) * get_elem b (k2 - 1) j)
                (decreases (k2 - 1 - k))
        = if k = k2 - 1 then ()
          else begin
            aux_split (k + 1);
            ()
          end
      in
      aux_split k1;
      ()
    end

// Standard multiply correctness: result[i][j] = dot_product
let lemma_standard_multiply_correct (a b:matrix{cols a == rows b}) (i:nat{i < rows a}) (j:nat{j < cols b})
  : Lemma (ensures get_elem (standard_multiply a b) i j == dot_product a b i j (cols a))
  = ()

// Submatrix properties
let lemma_submatrix_elem (m:matrix)
                         (row_start:nat) (row_end:nat{row_start < row_end /\ row_end <= rows m})
                         (col_start:nat) (col_end:nat{col_start < col_end /\ col_end <= cols m})
                         (i:nat{i < row_end - row_start}) (j:nat{j < col_end - col_start})
  : Lemma (ensures get_elem (submatrix m row_start row_end col_start col_end) i j ==
                   get_elem m (row_start + i) (col_start + j))
  = ()

// Matrix addition correctness
let lemma_matrix_add_elem (a b:matrix{rows a == rows b /\ cols a == cols b})
                          (i:nat{i < rows a}) (j:nat{j < cols a})
  : Lemma (ensures get_elem (matrix_add a b) i j == get_elem a i j + get_elem b i j)
  = ()

// Matrix subtraction correctness
let lemma_matrix_sub_elem (a b:matrix{rows a == rows b /\ cols a == cols b})
                          (i:nat{i < rows a}) (j:nat{j < cols a})
  : Lemma (ensures get_elem (matrix_sub a b) i j == get_elem a i j - get_elem b i j)
  = ()

// Assemble quadrants correctness
let lemma_assemble_quadrants_elem (c11 c12 c21 c22:matrix{
                                     rows c11 == rows c12 /\ 
                                     rows c11 == rows c21 /\ 
                                     rows c11 == rows c22 /\
                                     cols c11 == cols c12 /\ 
                                     cols c11 == cols c21 /\ 
                                     cols c11 == cols c22 /\
                                     rows c11 == cols c11})
                                  (i:nat{i < 2 * rows c11})
                                  (j:nat{j < 2 * cols c11})
  : Lemma (ensures (let m = assemble_quadrants c11 c12 c21 c22 in
                    let n = rows c11 in
                    get_elem m i j == (
                      if i < n && j < n then get_elem c11 i j
                      else if i < n && j >= n then get_elem c12 i (j - n)
                      else if i >= n && j < n then get_elem c21 (i - n) j
                      else get_elem c22 (i - n) (j - n))))
  = ()

// Main correctness theorem: Strassen equals standard multiply
// The full algebraic proof requires extensive case analysis and lemma chaining.
// We outline the key algebraic identities below:
//
// Standard multiply gives:
//   C11 = A11*B11 + A12*B21
//   C12 = A11*B12 + A12*B22
//   C21 = A21*B11 + A22*B21
//   C22 = A21*B12 + A22*B22
//
// Strassen computes (can be verified by expansion):
//   P5 + P4 - P2 + P6 = A11*B11 + A12*B21
//   P1 + P2           = A11*B12 + A12*B22
//   P3 + P4           = A21*B11 + A22*B21
//   P5 + P1 - P3 - P7 = A21*B12 + A22*B22

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"

// Helper lemmas for matrix algebra

// Helper: dot product distributes over matrix addition (left)
let rec lemma_dot_product_add_left
  (a1 a2 b:matrix{cols a1 == rows b /\ cols a2 == rows b /\ rows a1 == rows a2 /\ cols a1 == cols a2})
  (i:nat{i < rows a1}) (j:nat{j < cols b})
  (k:nat{k <= cols a1})
  : Lemma (ensures dot_product (matrix_add a1 a2) b i j k ==
                   dot_product a1 b i j k + dot_product a2 b i j k)
          (decreases k)
  = if k = 0 then ()
    else begin
      lemma_dot_product_add_left a1 a2 b i j (k - 1);
      lemma_matrix_add_elem a1 a2 i (k - 1);
      ()
    end

// Lemma: Product of matrix addition distributes correctly (left distributivity)
let lemma_matrix_product_add_left
  (a1 a2 b:matrix{cols a1 == rows b /\ cols a2 == rows b /\ rows a1 == rows a2 /\ cols a1 == cols a2})
  (i:nat{i < rows a1}) (j:nat{j < cols b})
  : Lemma (ensures get_elem (standard_multiply (matrix_add a1 a2) b) i j ==
                   get_elem (standard_multiply a1 b) i j + get_elem (standard_multiply a2 b) i j)
  = lemma_dot_product_add_left a1 a2 b i j (cols a1)

// Helper: dot product distributes over matrix addition (right)
let rec lemma_dot_product_add_right
  (a b1 b2:matrix{cols a == rows b1 /\ cols a == rows b2 /\ rows b1 == rows b2 /\ cols b1 == cols b2})
  (i:nat{i < rows a}) (j:nat{j < cols b1})
  (k:nat{k <= cols a})
  : Lemma (ensures dot_product a (matrix_add b1 b2) i j k ==
                   dot_product a b1 i j k + dot_product a b2 i j k)
          (decreases k)
  = if k = 0 then ()
    else begin
      lemma_dot_product_add_right a b1 b2 i j (k - 1);
      lemma_matrix_add_elem b1 b2 (k - 1) j;
      ()
    end

let lemma_matrix_product_add_right
  (a b1 b2:matrix{cols a == rows b1 /\ cols a == rows b2 /\ rows b1 == rows b2 /\ cols b1 == cols b2})
  (i:nat{i < rows a}) (j:nat{j < cols b1})
  : Lemma (ensures get_elem (standard_multiply a (matrix_add b1 b2)) i j ==
                   get_elem (standard_multiply a b1) i j + get_elem (standard_multiply a b2) i j)
  = lemma_dot_product_add_right a b1 b2 i j (cols a)

// Helper: dot product distributes over matrix subtraction (right)
let rec lemma_dot_product_sub_right
  (a b1 b2:matrix{cols a == rows b1 /\ cols a == rows b2 /\ rows b1 == rows b2 /\ cols b1 == cols b2})
  (i:nat{i < rows a}) (j:nat{j < cols b1})
  (k:nat{k <= cols a})
  : Lemma (ensures dot_product a (matrix_sub b1 b2) i j k ==
                   dot_product a b1 i j k - dot_product a b2 i j k)
          (decreases k)
  = if k = 0 then ()
    else begin
      lemma_dot_product_sub_right a b1 b2 i j (k - 1);
      lemma_matrix_sub_elem b1 b2 (k - 1) j;
      ()
    end

let lemma_matrix_product_sub_right
  (a b1 b2:matrix{cols a == rows b1 /\ cols a == rows b2 /\ rows b1 == rows b2 /\ cols b1 == cols b2})
  (i:nat{i < rows a}) (j:nat{j < cols b1})
  : Lemma (ensures get_elem (standard_multiply a (matrix_sub b1 b2)) i j ==
                   get_elem (standard_multiply a b1) i j - get_elem (standard_multiply a b2) i j)
  = lemma_dot_product_sub_right a b1 b2 i j (cols a)

// Helper: dot product distributes over matrix subtraction (left)
let rec lemma_dot_product_sub_left
  (a1 a2 b:matrix{cols a1 == rows b /\ cols a2 == rows b /\ rows a1 == rows a2 /\ cols a1 == cols a2})
  (i:nat{i < rows a1}) (j:nat{j < cols b})
  (k:nat{k <= cols a1})
  : Lemma (ensures dot_product (matrix_sub a1 a2) b i j k ==
                   dot_product a1 b i j k - dot_product a2 b i j k)
          (decreases k)
  = if k = 0 then ()
    else begin
      lemma_dot_product_sub_left a1 a2 b i j (k - 1);
      lemma_matrix_sub_elem a1 a2 i (k - 1);
      ()
    end

let lemma_matrix_product_sub_left
  (a1 a2 b:matrix{cols a1 == rows b /\ cols a2 == rows b /\ rows a1 == rows a2 /\ cols a1 == cols a2})
  (i:nat{i < rows a1}) (j:nat{j < cols b})
  : Lemma (ensures get_elem (standard_multiply (matrix_sub a1 a2) b) i j ==
                   get_elem (standard_multiply a1 b) i j - get_elem (standard_multiply a2 b) i j)
  = lemma_dot_product_sub_left a1 a2 b i j (cols a1)

// Helper lemma: dot product over quadrants
// For matrices divided at column/row 'half', the dot product splits
let lemma_dot_product_quadrant_split
  (a b:matrix{cols a == rows b})
  (i:nat{i < rows a}) (j:nat{j < cols b})
  (half:nat{half <= cols a /\ half <= rows b})
  : Lemma (ensures dot_product a b i j (cols a) ==
                   dot_product a b i j half + dot_product_aux a b i j half (cols a))
  = lemma_dot_product_split a b i j half (cols a)

/// When a matrix is square, pow2-sized, and has rows > 1,
/// half = rows/2 is a valid quadrant size: positive, pow2, and n - half == half.
/// Factored out so the simple arithmetic doesn't get combined with the
/// large VC of the main correctness proof (which causes VC explosion / timeout).
#push-options "--z3rlimit 10 --fuel 2 --ifuel 0"
let lemma_submatrix_square_pow2
  (m:matrix{is_square m /\ pow2_size m /\ rows m > 1})
  : Lemma (let n = rows m in
           let half = n / 2 in
           half > 0 /\
           is_pow2 half /\
           n - half == half)
  = lemma_pow2_half (rows m)
#pop-options

/// Connection lemma 1: dot_product on "left-column" and "top-row" submatrices
/// equals the first half of dot_product on the parent.
///
/// Concretely, for row offset ra and column offset cb:
///   dot_product (submatrix a ra (ra+h) 0 h) (submatrix b 0 h cb (cb+h)) i j k
///   == dot_product a b (ra+i) (cb+j) k
///
/// Proof: induction on k. At each step, submatrix element access reduces
/// definitionally via Seq.init/index to the parent element.
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let rec lemma_dot_product_submatrix_first
  (a b:matrix{cols a == rows b})
  (half:pos{2 * half == cols a /\ 2 * half == rows b})
  (ra:nat{ra + half <= rows a})
  (cb:nat{cb + half <= cols b})
  (i:nat{i < half}) (j:nat{j < half}) (k:nat{k <= half})
  : Lemma (ensures
      dot_product (submatrix a ra (ra + half) 0 half) (submatrix b 0 half cb (cb + half)) i j k
      == dot_product a b (ra + i) (cb + j) k)
    (decreases k)
  = if k = 0 then ()
    else begin
      lemma_dot_product_submatrix_first a b half ra cb i j (k - 1);
      // Inductive step: the k-1 tail matches by IH.
      // The head terms match because:
      //   get_elem (submatrix a ra (ra+h) 0 h) i (k-1) = get_elem a (ra+i) (0+k-1) = get_elem a (ra+i) (k-1)
      //   get_elem (submatrix b 0 h cb (cb+h)) (k-1) j = get_elem b (0+k-1) (cb+j)  = get_elem b (k-1) (cb+j)
      // These equalities hold by Seq.init/index reduction (no extra fuel needed).
      ()
    end
#pop-options

/// Connection lemma 2: dot_product_aux on the parent (from half to half+k)
/// equals dot_product_aux on "right-column" and "bottom-row" submatrices (from 0 to k).
///
/// Concretely:
///   dot_product_aux a b (ra+i) (cb+j) (half+k') (half+half)
///   == dot_product_aux (submatrix a ra (ra+h) h 2h) (submatrix b h 2h cb (cb+h)) i j k' half
///
/// Proof: induction (counting up from k' to half). At each step, the head
/// elements match via submatrix element reduction.
#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let rec lemma_dot_product_aux_submatrix_second
  (a b:matrix{cols a == rows b})
  (half:pos{2 * half == cols a /\ 2 * half == rows b})
  (ra:nat{ra + half <= rows a})
  (cb:nat{cb + half <= cols b})
  (i:nat{i < half}) (j:nat{j < half}) (k:nat{k <= half})
  : Lemma (ensures
      dot_product_aux a b (ra + i) (cb + j) (half + k) (half + half)
      == dot_product_aux (submatrix a ra (ra + half) half (half + half))
                         (submatrix b half (half + half) cb (cb + half))
                         i j k half)
    (decreases (half - k))
  = if k = half then ()
    else begin
      lemma_dot_product_aux_submatrix_second a b half ra cb i j (k + 1);
      // Inductive step: tails match by IH.
      // Head terms match because:
      //   get_elem a (ra+i) (half+k)  == get_elem (submatrix a ra (ra+h) h 2h) i k
      //   get_elem b (half+k) (cb+j)  == get_elem (submatrix b h 2h cb (cb+h)) k j
      ()
    end
#pop-options

/// Wrapper: standard_multiply decomposes via quadrants.
/// For element (ra+i, cb+j) of the product A*B, where both A and B are
/// square with side 2*half:
///
///   (A*B)[ra+i, cb+j] = (A_left * B_top)[i,j] + (A_right * B_bottom)[i,j]
///
/// where A_left = submatrix a ra (ra+h) 0 h, etc.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let lemma_standard_multiply_quadrant_decomp
  (a b:matrix{cols a == rows b /\ is_square a /\ is_square b})
  (half:pos{2 * half == rows a})
  (ra:nat{ra + half <= rows a})
  (cb:nat{cb + half <= cols b})
  (i:nat{i < half}) (j:nat{j < half})
  : Lemma (ensures (
      let a_left = submatrix a ra (ra + half) 0 half in
      let a_right = submatrix a ra (ra + half) half (2 * half) in
      let b_top = submatrix b 0 half cb (cb + half) in
      let b_bottom = submatrix b half (2 * half) cb (cb + half) in
      get_elem (standard_multiply a b) (ra + i) (cb + j) ==
        get_elem (standard_multiply a_left b_top) i j +
        get_elem (standard_multiply a_right b_bottom) i j))
  = let n = 2 * half in
    let a_left = submatrix a ra (ra + half) 0 half in
    let a_right = submatrix a ra (ra + half) half n in
    let b_top = submatrix b 0 half cb (cb + half) in
    let b_bottom = submatrix b half n cb (cb + half) in
    // (A*B)[ra+i, cb+j] = dot_product a b (ra+i) (cb+j) n
    lemma_standard_multiply_correct a b (ra + i) (cb + j);
    // Split: dot_product ... n = dot_product ... half + dot_product_aux ... half n
    lemma_dot_product_quadrant_split a b (ra + i) (cb + j) half;
    // First half: dot_product a b (ra+i) (cb+j) half = dot_product a_left b_top i j half
    lemma_dot_product_submatrix_first a b half ra cb i j half;
    // = standard_multiply a_left b_top [i,j]
    lemma_standard_multiply_correct a_left b_top i j;
    // Second half: dot_product_aux a b (ra+i) (cb+j) half n
    //   = dot_product_aux a_right b_bottom i j 0 half  (by connection lemma 2, with k=0)
    lemma_dot_product_aux_submatrix_second a b half ra cb i j 0;
    //   = dot_product a_right b_bottom i j 0 + dot_product_aux a_right b_bottom i j 0 half
    //   = 0 + dot_product_aux a_right b_bottom i j 0 half
    //   = dot_product a_right b_bottom i j half  (by split lemma, reversed)
    lemma_dot_product_split a_right b_bottom i j 0 half;
    //   = standard_multiply a_right b_bottom [i,j]
    lemma_standard_multiply_correct a_right b_bottom i j;
    ()
#pop-options

// Helper: prove element-wise equality for a specific element
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1 --split_queries always"
let rec lemma_strassen_elem_correct 
  (a b:matrix{cols a == rows b /\ is_square a /\ is_square b /\ pow2_size a})
  (i:nat{i < rows a}) (j:nat{j < cols b})
  : Lemma (ensures get_elem (strassen_multiply a b) i j == get_elem (standard_multiply a b) i j)
          (decreases rows a)
  = let n = rows a in
    if n = 1 then ()  // Base case: both use standard_multiply
    else begin
      let half = n / 2 in
      lemma_pow2_half n;
      
      // Extract quadrants  
      let a11 = submatrix a 0 half 0 half in
      let a12 = submatrix a 0 half half n in
      let a21 = submatrix a half n 0 half in
      let a22 = submatrix a half n half n in
      
      let b11 = submatrix b 0 half 0 half in
      let b12 = submatrix b 0 half half n in
      let b21 = submatrix b half n 0 half in
      let b22 = submatrix b half n half n in
      
      // Quadrant dimension arithmetic (isolated from main VC via helper lemma)
      // Core fact: n - half == half, so all quadrants are half×half
      lemma_submatrix_square_pow2 a;
      lemma_submatrix_square_pow2 b;
      assert (n - half == half);

      // All 8 quadrants are square (rows == cols == half) and pow2-sized
      // The submatrix return type gives rows/cols directly; n - half == half
      // makes the "off-diagonal" quadrants (a12, a21, etc.) square too.
      assert (is_square a11);
      assert (is_square a12);
      assert (is_square a21);
      assert (is_square a22);
      assert (is_square b11);
      assert (is_square b12);
      assert (is_square b21);
      assert (is_square b22);
      assert (pow2_size a11);
      assert (pow2_size a12);
      assert (pow2_size a21);
      assert (pow2_size a22);
      assert (pow2_size b11);
      assert (pow2_size b12);
      assert (pow2_size b21);
      assert (pow2_size b22);
      
      // Extract quadrants of the result by expanding strassen_multiply definition
      // strassen_multiply computes P1..P7 and assembles them into quadrants
      let p1 = strassen_multiply a11 (matrix_sub b12 b22) in
      let p2 = strassen_multiply (matrix_add a11 a12) b22 in
      let p3 = strassen_multiply (matrix_add a21 a22) b11 in
      let p4 = strassen_multiply a22 (matrix_sub b21 b11) in
      let p5 = strassen_multiply (matrix_add a11 a22) (matrix_add b11 b22) in
      let p6 = strassen_multiply (matrix_sub a12 a22) (matrix_add b21 b22) in
      let p7 = strassen_multiply (matrix_sub a11 a21) (matrix_add b11 b12) in
      
      let c11 = matrix_add (matrix_sub (matrix_add p5 p4) p2) p6 in
      let c12 = matrix_add p1 p2 in
      let c21 = matrix_add p3 p4 in
      let c22 = matrix_sub (matrix_sub (matrix_add p5 p1) p3) p7 in
      
      // strassen_multiply a b = assemble_quadrants c11 c12 c21 c22
      // (this follows by definition reduction)
      
      // Use assemble lemma to determine which quadrant (i,j) is in
      lemma_assemble_quadrants_elem c11 c12 c21 c22 i j;
      
      // Standard multiply also decomposes by quadrants
      lemma_standard_multiply_correct a b i j;
      
      // Case analysis on which quadrant the element falls into
      if i < half && j < half then begin
        // Upper-left quadrant: need to show c11[i,j] = (A11*B11 + A12*B21)[i,j]
        
        // Connect standard_multiply of quadrants to standard_multiply of parent
        lemma_standard_multiply_quadrant_decomp a b half 0 0 i j;
        
        // --- Build up Strassen algebra for P5 ---
        lemma_strassen_elem_correct (matrix_add a11 a22) (matrix_add b11 b22) i j;
        lemma_matrix_product_add_left a11 a22 (matrix_add b11 b22) i j;
        lemma_matrix_product_add_right a11 b11 b22 i j;
        lemma_matrix_product_add_right a22 b11 b22 i j;
        assert (get_elem p5 i j ==
                get_elem (standard_multiply a11 b11) i j +
                get_elem (standard_multiply a11 b22) i j +
                get_elem (standard_multiply a22 b11) i j +
                get_elem (standard_multiply a22 b22) i j)
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        
        // --- P4 ---
        lemma_strassen_elem_correct a22 (matrix_sub b21 b11) i j;
        lemma_matrix_product_sub_right a22 b21 b11 i j;
        assert (get_elem p4 i j ==
                get_elem (standard_multiply a22 b21) i j -
                get_elem (standard_multiply a22 b11) i j)
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        
        // --- P2 ---
        lemma_strassen_elem_correct (matrix_add a11 a12) b22 i j;
        lemma_matrix_product_add_left a11 a12 b22 i j;
        assert (get_elem p2 i j ==
                get_elem (standard_multiply a11 b22) i j +
                get_elem (standard_multiply a12 b22) i j)
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        
        // --- P6 ---
        lemma_strassen_elem_correct (matrix_sub a12 a22) (matrix_add b21 b22) i j;
        lemma_matrix_product_sub_left a12 a22 (matrix_add b21 b22) i j;
        lemma_matrix_product_add_right a12 b21 b22 i j;
        lemma_matrix_product_add_right a22 b21 b22 i j;
        assert (get_elem p6 i j ==
                get_elem (standard_multiply a12 b21) i j +
                get_elem (standard_multiply a12 b22) i j -
                get_elem (standard_multiply a22 b21) i j -
                get_elem (standard_multiply a22 b22) i j)
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        
        // --- Element access for c11 = ((p5+p4)-p2)+p6 ---
        lemma_matrix_add_elem p5 p4 i j;
        lemma_matrix_sub_elem (matrix_add p5 p4) p2 i j;
        lemma_matrix_add_elem (matrix_sub (matrix_add p5 p4) p2) p6 i j;
        
        // C11 = P5+P4-P2+P6 = A11*B11 + A12*B21 (pure linear arithmetic)
        assert (get_elem c11 i j ==
                get_elem (standard_multiply a11 b11) i j +
                get_elem (standard_multiply a12 b21) i j)
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        // Step 1: strassen_multiply a b at (i,j) = c11 at (i,j)
        assert (get_elem (strassen_multiply a b) i j == get_elem c11 i j)
          by (FStar.Tactics.SMT.smt_sync' 1 1);
        // Step 2: c11 at (i,j) = standard_multiply a b at (i,j)
        assert (get_elem c11 i j == get_elem (standard_multiply a b) i j)
          by (FStar.Tactics.SMT.smt_sync' 0 0)
      end
      else if i < half && j >= half then begin
        // Upper-right quadrant: C12 = P1 + P2 = A11*B12 + A12*B22
        let j' = j - half in
        
        // Apply IH to show P1 and P2 equal standard_multiply
        lemma_strassen_elem_correct a11 (matrix_sub b12 b22) i j';
        lemma_strassen_elem_correct (matrix_add a11 a12) b22 i j';
        
        // Expand algebraically
        lemma_matrix_product_sub_right a11 b12 b22 i j';
        lemma_matrix_product_add_left a11 a12 b22 i j';
        lemma_matrix_add_elem p1 p2 i j';
        
        // Element access
        lemma_standard_multiply_correct a11 b12 i j';
        lemma_standard_multiply_correct a11 b22 i j';
        lemma_standard_multiply_correct a12 b22 i j';
        
        // Relate submatrices to original
        lemma_submatrix_elem a 0 half 0 half i j';
        lemma_submatrix_elem a 0 half half n i j';
        lemma_submatrix_elem b 0 half half n i j';
        lemma_submatrix_elem b half n half n i j';
        
        // Standard multiply decomposition  
        lemma_standard_multiply_correct a b i j;
        lemma_dot_product_quadrant_split a b i j half;
        
        // Connect standard_multiply of quadrants to standard_multiply of parent
        // (A*B)[i,j] = (A*B)[0+i, half+j'] = (A11*B12)[i,j'] + (A12*B22)[i,j']
        lemma_standard_multiply_quadrant_decomp a b half 0 half i j';
        
        // Algebraic identity: P1+P2 = A11*B12 + A12*B22 at element (i,j')
        assert (get_elem c12 i j' ==
                get_elem (standard_multiply a11 b12) i j' +
                get_elem (standard_multiply a12 b22) i j')
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        // Step 1: strassen_multiply a b at (i,j) = c12 at (i,j')
        assert (get_elem (strassen_multiply a b) i j == get_elem c12 i j')
          by (FStar.Tactics.SMT.smt_sync' 1 1);
        // Step 2: c12 at (i,j') = standard_multiply a b at (i,j)
        assert (get_elem c12 i j' == get_elem (standard_multiply a b) i j)
          by (FStar.Tactics.SMT.smt_sync' 0 0)
      end
      else if i >= half && j < half then begin
        // Lower-left quadrant: C21 = P3 + P4 = A21*B11 + A22*B21
        let i' = i - half in
        
        lemma_strassen_elem_correct (matrix_add a21 a22) b11 i' j;
        lemma_strassen_elem_correct a22 (matrix_sub b21 b11) i' j;
        
        lemma_matrix_product_add_left a21 a22 b11 i' j;
        lemma_matrix_product_sub_right a22 b21 b11 i' j;
        lemma_matrix_add_elem p3 p4 i' j;
        
        lemma_standard_multiply_correct a21 b11 i' j;
        lemma_standard_multiply_correct a22 b11 i' j;
        lemma_standard_multiply_correct a22 b21 i' j;
        
        lemma_submatrix_elem a half n 0 half i' j;
        lemma_submatrix_elem a half n half n i' j;
        lemma_submatrix_elem b 0 half 0 half i' j;
        lemma_submatrix_elem b half n 0 half i' j;
        
        lemma_standard_multiply_correct a b i j;
        lemma_dot_product_quadrant_split a b i j half;
        
        // Connect standard_multiply of quadrants to standard_multiply of parent
        // (A*B)[i,j] = (A*B)[half+i', 0+j] = (A21*B11)[i',j] + (A22*B21)[i',j]
        lemma_standard_multiply_quadrant_decomp a b half half 0 i' j;
        
        // Algebraic identity: P3+P4 = A21*B11 + A22*B21 at element (i',j)
        assert (get_elem c21 i' j ==
                get_elem (standard_multiply a21 b11) i' j +
                get_elem (standard_multiply a22 b21) i' j)
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        // Step 1: strassen_multiply a b at (i,j) = c21 at (i',j)
        // (uses fuel 1 to unfold strassen_multiply once + assemble_quadrants_elem)
        assert (get_elem (strassen_multiply a b) i j == get_elem c21 i' j)
          by (FStar.Tactics.SMT.smt_sync' 1 1);
        // Step 2: c21 at (i',j) = standard_multiply a b at (i,j)
        // (pure arithmetic + decomp lemma, no unfolding needed)
        assert (get_elem c21 i' j == get_elem (standard_multiply a b) i j)
          by (FStar.Tactics.SMT.smt_sync' 0 0)
      end
      else begin
        // Lower-right quadrant: C22 = P5 + P1 - P3 - P7 = A21*B12 + A22*B22
        let i' = i - half in
        let j' = j - half in
        
        // Connect standard_multiply of quadrants to standard_multiply of parent
        lemma_standard_multiply_quadrant_decomp a b half half half i' j';
        
        // --- Build up Strassen algebra for P5 ---
        lemma_strassen_elem_correct (matrix_add a11 a22) (matrix_add b11 b22) i' j';
        lemma_matrix_product_add_left a11 a22 (matrix_add b11 b22) i' j';
        lemma_matrix_product_add_right a11 b11 b22 i' j';
        lemma_matrix_product_add_right a22 b11 b22 i' j';
        assert (get_elem p5 i' j' ==
                get_elem (standard_multiply a11 b11) i' j' +
                get_elem (standard_multiply a11 b22) i' j' +
                get_elem (standard_multiply a22 b11) i' j' +
                get_elem (standard_multiply a22 b22) i' j')
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        
        // --- P1 ---
        lemma_strassen_elem_correct a11 (matrix_sub b12 b22) i' j';
        lemma_matrix_product_sub_right a11 b12 b22 i' j';
        assert (get_elem p1 i' j' ==
                get_elem (standard_multiply a11 b12) i' j' -
                get_elem (standard_multiply a11 b22) i' j')
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        
        // --- P3 ---
        lemma_strassen_elem_correct (matrix_add a21 a22) b11 i' j';
        lemma_matrix_product_add_left a21 a22 b11 i' j';
        assert (get_elem p3 i' j' ==
                get_elem (standard_multiply a21 b11) i' j' +
                get_elem (standard_multiply a22 b11) i' j')
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        
        // --- P7 ---
        lemma_strassen_elem_correct (matrix_sub a11 a21) (matrix_add b11 b12) i' j';
        lemma_matrix_product_sub_left a11 a21 (matrix_add b11 b12) i' j';
        lemma_matrix_product_add_right a11 b11 b12 i' j';
        lemma_matrix_product_add_right a21 b11 b12 i' j';
        assert (get_elem p7 i' j' ==
                get_elem (standard_multiply a11 b11) i' j' +
                get_elem (standard_multiply a11 b12) i' j' -
                get_elem (standard_multiply a21 b11) i' j' -
                get_elem (standard_multiply a21 b12) i' j')
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        
        // --- Element access for c22 = ((p5+p1)-p3)-p7 ---
        lemma_matrix_add_elem p5 p1 i' j';
        lemma_matrix_sub_elem (matrix_add p5 p1) p3 i' j';
        lemma_matrix_sub_elem (matrix_sub (matrix_add p5 p1) p3) p7 i' j';
        
        // C22 = P5+P1-P3-P7 = A21*B12 + A22*B22 (pure linear arithmetic)
        assert (get_elem c22 i' j' ==
                get_elem (standard_multiply a21 b12) i' j' +
                get_elem (standard_multiply a22 b22) i' j')
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        // Step 1: strassen_multiply a b at (i,j) = c22 at (i',j')
        assert (get_elem (strassen_multiply a b) i j == get_elem c22 i' j')
          by (FStar.Tactics.SMT.smt_sync' 1 1);
        // Step 2: c22 at (i',j') = standard_multiply a b at (i,j)
        assert (get_elem c22 i' j' == get_elem (standard_multiply a b) i j)
          by (FStar.Tactics.SMT.smt_sync' 0 0)
      end
    end
#pop-options

//SNIPPET_START: strassen_correct
let lemma_strassen_correct (a b:matrix{cols a == rows b /\ is_square a /\ is_square b /\ pow2_size a})
  : Lemma (ensures (forall (i:nat) (j:nat). i < rows a /\ j < cols b ==>
                    get_elem (strassen_multiply a b) i j == get_elem (standard_multiply a b) i j))
  = // Prove for all elements
    let aux (i:nat{i < rows a}) (j:nat{j < cols b})
      : Lemma (get_elem (strassen_multiply a b) i j == get_elem (standard_multiply a b) i j)
      = lemma_strassen_elem_correct a b i j
    in
    FStar.Classical.forall_intro_2 aux
//SNIPPET_END: strassen_correct

#pop-options

#pop-options
