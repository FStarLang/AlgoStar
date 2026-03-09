module CLRS.Ch10.SinglyLinkedList.Spec

open FStar.List.Tot

(* Pure specification of linked list operations on list int *)

(** 1. Define linked list as list int *)
type linked_list_spec = list int

(** 2. Insert element at head *)
let list_insert_head (l: list int) (x: int) : list int = 
  x :: l

(** 3. Search for element in list *)
let list_search (l: list int) (x: int) : bool = 
  mem x l

(** 4. Delete first occurrence of element *)
let rec list_delete (l: list int) (x: int) : list int =
  match l with
  | [] -> []
  | hd :: tl -> 
      if hd = x then tl
      else hd :: list_delete tl x

(** 9. Length of list *)
let list_length (l: list int) : nat = 
  length l

(** Helper: Count occurrences of element in list *)
let rec count (x: int) (l: list int) : nat =
  match l with
  | [] -> 0
  | hd :: tl -> 
      if hd = x then 1 + count x tl
      else count x tl

(** Helper lemma: mem is equivalent to count > 0 *)
let rec lemma_mem_count (x: int) (l: list int)
  : Lemma (ensures mem x l <==> count x l > 0)
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl -> lemma_mem_count x tl

(** Helper lemma: count in tail *)
let lemma_count_tail (x: int) (hd: int) (tl: list int)
  : Lemma (ensures count x (hd :: tl) == (if hd = x then 1 + count x tl else count x tl))
  = ()

(** Helper lemma: delete reduces count by at most 1 *)
let rec lemma_delete_count (l: list int) (x: int)
  : Lemma (ensures (let l' = list_delete l x in
                    count x l' <= count x l /\
                    (count x l > 0 ==> count x l' == count x l - 1) /\
                    (count x l == 0 ==> count x l' == 0)))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
        if hd = x then ()
        else lemma_delete_count tl x

(** Helper lemma: delete preserves count of other elements *)
let rec lemma_delete_preserves_other (l: list int) (x: int) (y: int)
  : Lemma (requires y <> x)
          (ensures count y (list_delete l x) == count y l)
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
        if hd = x then ()
        else lemma_delete_preserves_other tl x y

(** Helper lemma: list_delete reduces length by at most 1 *)
let rec lemma_delete_length (l: list int) (x: int)
  : Lemma (ensures (let l' = list_delete l x in
                    length l' <= length l /\
                    (mem x l ==> length l' == length l - 1) /\
                    (~(mem x l) ==> length l' == length l)))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
        if hd = x then ()
        else lemma_delete_length tl x

(** 5. Prove: inserting x makes x searchable *)
let lemma_insert_search (l: list int) (x: int)
  : Lemma (ensures list_search (list_insert_head l x) x == true)
  = ()

(** 6. Prove: inserting x doesn't affect search for different element *)
let lemma_insert_search_other (l: list int) (x: int) (y: int)
  : Lemma (requires y <> x)
          (ensures list_search (list_insert_head l x) y == list_search l y)
  = ()

(** 7. Prove: deleting non-existent element is identity *)
let rec lemma_delete_not_found (l: list int) (x: int)
  : Lemma (requires ~(list_search l x))
          (ensures list_delete l x == l)
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl -> 
        assert (hd <> x);
        lemma_delete_not_found tl x

(** 8. Prove: deleting single occurrence removes it *)
let lemma_delete_single_occurrence (l: list int) (x: int)
  : Lemma (requires count x l == 1)
          (ensures ~(list_search (list_delete l x) x))
  = lemma_delete_count l x;
    let l' = list_delete l x in
    assert (count x l' == 0);
    lemma_mem_count x l'

(** 10. Prove: inserting increases length by 1 *)
let lemma_insert_length (l: list int) (x: int)
  : Lemma (ensures list_length (list_insert_head l x) == list_length l + 1)
  = ()

(** 11. Prove: deleting existing element reduces length by 1 *)
let lemma_delete_length_decreases (l: list int) (x: int)
  : Lemma (requires list_search l x)
          (ensures list_length (list_delete l x) == list_length l - 1)
  = lemma_delete_length l x

(** Additional useful lemmas for completeness *)

(** Lemma: delete followed by insert restores element *)
let lemma_delete_insert_restore (l: list int) (x: int)
  : Lemma (ensures mem x (list_insert_head (list_delete l x) x))
  = ()

(** Lemma: inserting then deleting same element removes it from head *)
let lemma_insert_delete_head (l: list int) (x: int)
  : Lemma (ensures list_delete (list_insert_head l x) x == l)
  = ()

(** Lemma: delete is idempotent when element not present *)
let lemma_delete_idempotent (l: list int) (x: int)
  : Lemma (requires ~(mem x l))
          (ensures list_delete (list_delete l x) x == list_delete l x)
  = lemma_delete_not_found l x;
    assert (list_delete l x == l);
    lemma_delete_not_found (list_delete l x) x

(** Lemma: length is always non-negative *)
let lemma_length_nonneg (l: list int)
  : Lemma (ensures list_length l >= 0)
  = ()

(** Lemma: empty list has length 0 *)
let lemma_empty_length ()
  : Lemma (ensures list_length [] == 0)
  = ()

(** Lemma: non-empty list has positive length *)
let lemma_nonempty_length (l: list int)
  : Lemma (requires l =!= [])
          (ensures list_length l > 0)
  = ()

(** Lemma: search in empty list returns false *)
let lemma_search_empty (x: int)
  : Lemma (ensures list_search [] x == false)
  = ()

(** Lemma: delete from empty list returns empty *)
let lemma_delete_empty (x: int)
  : Lemma (ensures list_delete [] x == [])
  = ()

(** Theorem: All basic operations are well-defined and correct *)
let theorem_operations_correct ()
  : Lemma (ensures 
      // Insert makes element searchable
      (forall (l: list int) (x: int). list_search (list_insert_head l x) x == true) /\
      // Insert preserves other elements
      (forall (l: list int) (x y: int). y <> x ==> 
        list_search (list_insert_head l x) y == list_search l y) /\
      // Delete non-existent is identity
      (forall (l: list int) (x: int). ~(list_search l x) ==> list_delete l x == l) /\
      // Delete single occurrence removes it
      (forall (l: list int) (x: int). count x l == 1 ==> 
        ~(list_search (list_delete l x) x)) /\
      // Insert increases length
      (forall (l: list int) (x: int). 
        list_length (list_insert_head l x) == list_length l + 1) /\
      // Delete decreases length
      (forall (l: list int) (x: int). list_search l x ==> 
        list_length (list_delete l x) == list_length l - 1))
  = let prove_insert_search (l: list int) (x: int) 
      : Lemma (list_search (list_insert_head l x) x == true)
      = lemma_insert_search l x
    in
    let prove_insert_other (l: list int) (x: int) (y: int)
      : Lemma (y <> x ==> list_search (list_insert_head l x) y == list_search l y)
      = if y <> x then lemma_insert_search_other l x y
    in
    let prove_delete_not_found (l: list int) (x: int)
      : Lemma (~(list_search l x) ==> list_delete l x == l)
      = if not (list_search l x) then lemma_delete_not_found l x
    in
    let prove_delete_single (l: list int) (x: int)
      : Lemma (count x l == 1 ==> ~(list_search (list_delete l x) x))
      = if count x l = 1 then lemma_delete_single_occurrence l x
    in
    let prove_insert_length (l: list int) (x: int)
      : Lemma (list_length (list_insert_head l x) == list_length l + 1)
      = lemma_insert_length l x
    in
    let prove_delete_length (l: list int) (x: int)
      : Lemma (list_search l x ==> list_length (list_delete l x) == list_length l - 1)
      = if list_search l x then lemma_delete_length_decreases l x
    in
    FStar.Classical.forall_intro_2 prove_insert_search;
    FStar.Classical.forall_intro_3 prove_insert_other;
    FStar.Classical.forall_intro_2 prove_delete_not_found;
    FStar.Classical.forall_intro_2 prove_delete_single;
    FStar.Classical.forall_intro_2 prove_insert_length;
    FStar.Classical.forall_intro_2 prove_delete_length
