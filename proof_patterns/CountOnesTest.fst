module CountOnesTest
open FStar.Seq
open FStar.Mul

(* Count elements equal to 1 in s[0..k) *)
let rec count_ones (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Tot (r: nat{r <= k}) (decreases k)
  = if k = 0 then 0
    else (if Seq.index s (k - 1) = 1 then 1 else 0) + count_ones s (k - 1)

(* If any element in s[0..k) is not 1, count < k *)
let rec count_ones_lt (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat)
  : Lemma
    (requires j < k /\ Seq.index s j <> 1)
    (ensures count_ones s k < k)
    (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then
      () // Seq.index s (k-1) <> 1, so we add 0, and count_ones s (k-1) <= k-1
    else
      count_ones_lt s (k - 1) j // j < k-1, recurse

(* Updating index j to 1 when it wasn't 1: count goes up by 1 *)
let rec count_ones_upd_to_one (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat)
  : Lemma
    (requires j < k /\ Seq.index s j <> 1 /\ k <= Seq.length s)
    (ensures
      Seq.length (Seq.upd s j 1) == Seq.length s /\
      count_ones (Seq.upd s j 1) k == count_ones s k + 1)
    (decreases k)
  = if k = 0 then ()
    else begin
      let s' = Seq.upd s j 1 in
      assert (Seq.length s' == Seq.length s);
      if j = k - 1 then begin
        // At position k-1: s[k-1] <> 1 contributed 0, s'[k-1] = 1 contributes 1
        // For positions < k-1, s and s' agree
        assert (Seq.index s' (k-1) = 1);
        assert (Seq.index s (k-1) <> 1);
        // count_ones s' (k-1) == count_ones s (k-1) since upd at k-1 doesn't affect [0..k-1)
        let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s})
          : Lemma (ensures Seq.length (Seq.upd s j 1) == Seq.length s /\
                           count_ones (Seq.upd s j 1) k' == count_ones s k')
                  (decreases k')
          = if k' = 0 then ()
            else begin
              assert (Seq.index (Seq.upd s j 1) (k'-1) == Seq.index s (k'-1));
              aux s (k'-1) j
            end
        in
        aux s (k-1) j
      end
      else begin
        // j < k-1: recurse
        assert (Seq.index s' (k-1) == Seq.index s (k-1));
        count_ones_upd_to_one s (k-1) j
      end
    end

(* Updating index j from 1 to something else: count goes down by 1 *)
let rec count_ones_upd_from_one (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat) (v: int)
  : Lemma
    (requires j < k /\ Seq.index s j = 1 /\ v <> 1 /\ k <= Seq.length s)
    (ensures
      Seq.length (Seq.upd s j v) == Seq.length s /\
      count_ones (Seq.upd s j v) k == count_ones s k - 1)
    (decreases k)
  = if k = 0 then ()
    else begin
      let s' = Seq.upd s j v in
      if j = k - 1 then begin
        let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s}) (v: int)
          : Lemma (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                           count_ones (Seq.upd s j v) k' == count_ones s k')
                  (decreases k')
          = if k' = 0 then ()
            else begin
              assert (Seq.index (Seq.upd s j v) (k'-1) == Seq.index s (k'-1));
              aux s (k'-1) j v
            end
        in
        aux s (k-1) j v
      end
      else begin
        assert (Seq.index s' (k-1) == Seq.index s (k-1));
        count_ones_upd_from_one s (k-1) j v
      end
    end

(* Updating out of range [0..k) doesn't change count *)
let rec count_ones_upd_out (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat) (v: int)
  : Lemma
    (requires j >= k /\ j < Seq.length s)
    (ensures
      Seq.length (Seq.upd s j v) == Seq.length s /\
      count_ones (Seq.upd s j v) k == count_ones s k)
    (decreases k)
  = if k = 0 then ()
    else begin
      assert (Seq.index (Seq.upd s j v) (k-1) == Seq.index s (k-1));
      count_ones_upd_out s (k-1) j v
    end
