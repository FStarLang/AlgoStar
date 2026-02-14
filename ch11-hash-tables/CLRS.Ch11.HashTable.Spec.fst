module CLRS.Ch11.HashTable.Spec

open FStar.Classical

(** Pure specification for hash tables using association lists *)

(** Hash table model: association list mapping keys to values *)
type ht_model = list (nat & int)

(** Empty hash table *)
let ht_empty : ht_model = []

(** Search for a key in the association list *)
let rec ht_search (m: ht_model) (key: nat) : option int =
  match m with
  | [] -> None
  | (k, v) :: rest ->
    if k = key then Some v
    else ht_search rest key

(** Insert a key-value pair (adds to front, shadowing any existing binding) *)
let ht_insert (m: ht_model) (key: nat) (value: int) : ht_model =
  (key, value) :: m

(** Delete a key from the association list *)
let rec ht_delete (m: ht_model) (key: nat) : ht_model =
  match m with
  | [] -> []
  | (k, v) :: rest ->
    if k = key then ht_delete rest key
    else (k, v) :: ht_delete rest key

(** Lemma: Searching in empty table returns None *)
let lemma_search_empty (k: nat)
  : Lemma (ht_search ht_empty k == None)
  = ()

(** Lemma: Insert then search same key returns the inserted value *)
let lemma_insert_search_same (m: ht_model) (k: nat) (v: int)
  : Lemma (ht_search (ht_insert m k v) k == Some v)
  = ()

(** Lemma: Insert doesn't affect other keys *)
let rec lemma_insert_search_other (m: ht_model) (k1: nat) (k2: nat) (v: int)
  : Lemma 
    (requires k1 <> k2)
    (ensures ht_search (ht_insert m k1 v) k2 == ht_search m k2)
    (decreases m)
  = match m with
    | [] -> ()
    | (k, _) :: rest -> 
      if k = k2 then ()
      else lemma_insert_search_other rest k1 k2 v

(** Lemma: Delete removes the key *)
let rec lemma_delete_search_same (m: ht_model) (k: nat)
  : Lemma 
    (ensures ht_search (ht_delete m k) k == None)
    (decreases m)
  = match m with
    | [] -> ()
    | (k', _) :: rest ->
      if k' = k then lemma_delete_search_same rest k
      else lemma_delete_search_same rest k

(** Lemma: Delete doesn't affect other keys *)
let rec lemma_delete_search_other (m: ht_model) (k1: nat) (k2: nat)
  : Lemma
    (requires k1 <> k2)
    (ensures ht_search (ht_delete m k1) k2 == ht_search m k2)
    (decreases m)
  = match m with
    | [] -> ()
    | (k, v) :: rest ->
      if k = k1 then lemma_delete_search_other rest k1 k2
      else lemma_delete_search_other rest k1 k2

(** Lemma: Multiple inserts of same key, last one wins *)
let lemma_insert_insert_same (m: ht_model) (k: nat) (v1: int) (v2: int)
  : Lemma (ht_search (ht_insert (ht_insert m k v1) k v2) k == Some v2)
  = ()

(** Lemma: Deleting from empty gives empty *)
let lemma_delete_empty (k: nat)
  : Lemma (ht_delete ht_empty k == ht_empty)
  = ()

(** Lemma: Insert then delete same key *)
let rec lemma_insert_delete_same (m: ht_model) (k: nat) (v: int)
  : Lemma (ht_delete (ht_insert m k v) k == ht_delete m k)
  = match m with
    | [] -> ()
    | (k', _) :: rest ->
      if k' = k then ()
      else lemma_insert_delete_same rest k v

(** Lemma: Delete then insert restores the key *)
let lemma_delete_insert (m: ht_model) (k: nat) (v: int)
  : Lemma (ht_search (ht_insert (ht_delete m k) k v) k == Some v)
  = ()

(** Lemma: Commutativity of deletes *)
let rec lemma_delete_commutes (m: ht_model) (k1: nat) (k2: nat)
  : Lemma (ht_delete (ht_delete m k1) k2 == ht_delete (ht_delete m k2) k1)
  = match m with
    | [] -> ()
    | (k, v) :: rest ->
      if k = k1 && k = k2 then lemma_delete_commutes rest k1 k2
      else if k = k1 then lemma_delete_commutes rest k1 k2
      else if k = k2 then lemma_delete_commutes rest k1 k2
      else lemma_delete_commutes rest k1 k2

(** Helper: membership in the model *)
let rec mem (m: ht_model) (key: nat) : bool =
  match m with
  | [] -> false
  | (k, _) :: rest ->
    if k = key then true
    else mem rest key

(** Lemma: mem is equivalent to search returning Some *)
let rec lemma_mem_search (m: ht_model) (k: nat)
  : Lemma (mem m k <==> Some? (ht_search m k))
  = match m with
    | [] -> ()
    | (k', _) :: rest ->
      if k' = k then ()
      else lemma_mem_search rest k

(** Lemma: Insert makes key present *)
let lemma_insert_mem (m: ht_model) (k: nat) (v: int)
  : Lemma (mem (ht_insert m k v) k)
  = ()

(** Lemma: Delete makes key absent *)
let rec lemma_delete_not_mem (m: ht_model) (k: nat)
  : Lemma (not (mem (ht_delete m k) k))
  = match m with
    | [] -> ()
    | (k', _) :: rest ->
      if k' = k then lemma_delete_not_mem rest k
      else lemma_delete_not_mem rest k

(** Idempotence of delete *)
let rec lemma_delete_idempotent (m: ht_model) (k: nat)
  : Lemma (ht_delete (ht_delete m k) k == ht_delete m k)
  = match m with
    | [] -> ()
    | (k', v) :: rest ->
      if k' = k then lemma_delete_idempotent rest k
      else lemma_delete_idempotent rest k

(** Insert different keys is order-independent for search *)
let lemma_insert_commutes_search (m: ht_model) (k1: nat) (k2: nat) (v1: int) (v2: int) (k: nat)
  : Lemma
    (requires k1 <> k2)
    (ensures ht_search (ht_insert (ht_insert m k1 v1) k2 v2) k ==
             ht_search (ht_insert (ht_insert m k2 v2) k1 v1) k)
  = if k = k1 then ()
    else if k = k2 then ()
    else lemma_insert_search_other (ht_insert m k1 v1) k2 k v2

(** Size of hash table (number of entries, including duplicates) *)
let rec ht_size (m: ht_model) : nat =
  match m with
  | [] -> 0
  | _ :: rest -> 1 + ht_size rest

(** Lemma: Empty has size 0 *)
let lemma_empty_size ()
  : Lemma (ht_size ht_empty == 0)
  = ()

(** Lemma: Insert increases size by 1 *)
let lemma_insert_size (m: ht_model) (k: nat) (v: int)
  : Lemma (ht_size (ht_insert m k v) == 1 + ht_size m)
  = ()

(** Lemma: Delete decreases or maintains size *)
let rec lemma_delete_size (m: ht_model) (k: nat)
  : Lemma (ht_size (ht_delete m k) <= ht_size m)
  = match m with
    | [] -> ()
    | (k', _) :: rest ->
      if k' = k then lemma_delete_size rest k
      else lemma_delete_size rest k

(** Keys in the model *)
let rec keys (m: ht_model) : list nat =
  match m with
  | [] -> []
  | (k, _) :: rest -> k :: keys rest

(** Membership in a list of keys *)
let rec mem_key (k: nat) (ks: list nat) : bool =
  match ks with
  | [] -> false
  | k' :: rest -> k' = k || mem_key k rest

(** Lemma: Search result implies key is in keys list *)
let rec lemma_search_in_keys (m: ht_model) (k: nat) (v: int)
  : Lemma
    (requires ht_search m k == Some v)
    (ensures mem_key k (keys m))
  = match m with
    | [] -> ()
    | (k', v') :: rest ->
      if k' = k then ()
      else lemma_search_in_keys rest k v
