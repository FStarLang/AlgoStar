(*
   Strassen's Algorithm — Correctness Proofs (CLRS §4.2)
   
   Proves Strassen's algorithm produces the same result as standard matrix
   multiplication, via element-wise algebraic verification of the Strassen
   formulas in each quadrant.
*)

module CLRS.Ch04.Strassen.Lemmas
open FStar.Mul
open FStar.Seq
open FStar.Math.Lemmas
open FStar.Classical
open CLRS.Ch04.Strassen.Spec

module Seq = FStar.Seq

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"

// Helper: auxiliary sum function for dot product
let rec dot_product_aux (a b:matrix{cols a == rows b})
                        (i:nat{i < rows a}) (j:nat{j < cols b})
                        (k1 k2:nat{k1 <= k2 /\ k2 <= cols a})
  : Tot int
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
      lemma_dot_product_split a b i j k1 (k2 - 1);
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
let lemma_dot_product_quadrant_split
  (a b:matrix{cols a == rows b})
  (i:nat{i < rows a}) (j:nat{j < cols b})
  (half:nat{half <= cols a /\ half <= rows b})
  : Lemma (ensures dot_product a b i j (cols a) ==
                   dot_product a b i j half + dot_product_aux a b i j half (cols a))
  = lemma_dot_product_split a b i j half (cols a)

/// When a matrix is square, pow2-sized, and has rows > 1,
/// half = rows/2 is a valid quadrant size: positive, pow2, and n - half == half.
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
      ()
    end
#pop-options

/// Connection lemma 2: dot_product_aux on the parent (from half to half+k)
/// equals dot_product_aux on "right-column" and "bottom-row" submatrices.
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
      ()
    end
#pop-options

/// Wrapper: standard_multiply decomposes via quadrants.
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
    lemma_standard_multiply_correct a b (ra + i) (cb + j);
    lemma_dot_product_quadrant_split a b (ra + i) (cb + j) half;
    lemma_dot_product_submatrix_first a b half ra cb i j half;
    lemma_standard_multiply_correct a_left b_top i j;
    lemma_dot_product_aux_submatrix_second a b half ra cb i j 0;
    lemma_dot_product_split a_right b_bottom i j 0 half;
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
      
      // Quadrant dimension arithmetic
      lemma_submatrix_square_pow2 a;
      lemma_submatrix_square_pow2 b;
      assert (n - half == half);

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
      
      lemma_assemble_quadrants_elem c11 c12 c21 c22 i j;
      
      lemma_standard_multiply_correct a b i j;
      
      if i < half && j < half then begin
        // Upper-left quadrant: need to show c11[i,j] = (A11*B11 + A12*B21)[i,j]
        
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
        assert (get_elem (strassen_multiply a b) i j == get_elem c11 i j)
          by (FStar.Tactics.SMT.smt_sync' 1 1);
        assert (get_elem c11 i j == get_elem (standard_multiply a b) i j)
          by (FStar.Tactics.SMT.smt_sync' 0 0)
      end
      else if i < half && j >= half then begin
        // Upper-right quadrant: C12 = P1 + P2 = A11*B12 + A12*B22
        let j' = j - half in
        
        lemma_strassen_elem_correct a11 (matrix_sub b12 b22) i j';
        lemma_strassen_elem_correct (matrix_add a11 a12) b22 i j';
        
        lemma_matrix_product_sub_right a11 b12 b22 i j';
        lemma_matrix_product_add_left a11 a12 b22 i j';
        lemma_matrix_add_elem p1 p2 i j';
        
        lemma_standard_multiply_correct a11 b12 i j';
        lemma_standard_multiply_correct a11 b22 i j';
        lemma_standard_multiply_correct a12 b22 i j';
        
        lemma_submatrix_elem a 0 half 0 half i j';
        lemma_submatrix_elem a 0 half half n i j';
        lemma_submatrix_elem b 0 half half n i j';
        lemma_submatrix_elem b half n half n i j';
        
        lemma_standard_multiply_correct a b i j;
        lemma_dot_product_quadrant_split a b i j half;
        
        lemma_standard_multiply_quadrant_decomp a b half 0 half i j';
        
        assert (get_elem c12 i j' ==
                get_elem (standard_multiply a11 b12) i j' +
                get_elem (standard_multiply a12 b22) i j')
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        assert (get_elem (strassen_multiply a b) i j == get_elem c12 i j')
          by (FStar.Tactics.SMT.smt_sync' 1 1);
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
        
        lemma_standard_multiply_quadrant_decomp a b half half 0 i' j;
        
        assert (get_elem c21 i' j ==
                get_elem (standard_multiply a21 b11) i' j +
                get_elem (standard_multiply a22 b21) i' j)
          by (FStar.Tactics.SMT.smt_sync' 0 0);
        assert (get_elem (strassen_multiply a b) i j == get_elem c21 i' j)
          by (FStar.Tactics.SMT.smt_sync' 1 1);
        assert (get_elem c21 i' j == get_elem (standard_multiply a b) i j)
          by (FStar.Tactics.SMT.smt_sync' 0 0)
      end
      else begin
        // Lower-right quadrant: C22 = P5 + P1 - P3 - P7 = A21*B12 + A22*B22
        let i' = i - half in
        let j' = j - half in
        
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
        assert (get_elem (strassen_multiply a b) i j == get_elem c22 i' j')
          by (FStar.Tactics.SMT.smt_sync' 1 1);
        assert (get_elem c22 i' j' == get_elem (standard_multiply a b) i j)
          by (FStar.Tactics.SMT.smt_sync' 0 0)
      end
    end
#pop-options

//SNIPPET_START: strassen_correct
let lemma_strassen_correct (a b:matrix{cols a == rows b /\ is_square a /\ is_square b /\ pow2_size a})
  : Lemma (ensures (forall (i:nat) (j:nat). i < rows a /\ j < cols b ==>
                    get_elem (strassen_multiply a b) i j == get_elem (standard_multiply a b) i j))
  = let aux (i:nat{i < rows a}) (j:nat{j < cols b})
      : Lemma (get_elem (strassen_multiply a b) i j == get_elem (standard_multiply a b) i j)
      = lemma_strassen_elem_correct a b i j
    in
    FStar.Classical.forall_intro_2 aux
//SNIPPET_END: strassen_correct
