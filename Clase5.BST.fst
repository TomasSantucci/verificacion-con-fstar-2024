module Clase5.BST

open FStar.Mul
open FStar.List.Tot

let max (x y : int) : int = if x > y then x else y

type bst =
  | L
  | N of bst & int & bst

let rec insert (x: int) (t: bst) : bst =
  match t with
  | L -> N (L, x, L)
  | N (l, y, r) ->
    (* Nota: admite duplicados *)
    if x <= y
    then N (insert x l, y, r)
    else N (l, y, insert x r)

let rec member (x: int) (t: bst) : bool =
  match t with
  | L -> false
  | N (l, y, r) ->
    if x < y then member x l
    else if x > y then member x r
    else true

let rec to_list (t: bst) : list int =
  match t with
  | L -> []
  | N (l, x, r) -> to_list l @ [x] @ to_list r

let rec from_list (l: list int) : bst =
  match l with
  | [] -> L
  | x :: xs -> insert x (from_list xs)

let rec size (t: bst) : nat =
  match t with
  | L -> 0
  | N (l, _, r) -> 1 + size l + size r

let rec height (t: bst) : nat =
  match t with
  | L -> 0
  | N (l, _, r) -> 1 + max (height l) (height r)

let rec insert_size (x:int) (t:bst) : Lemma (size (insert x t) == 1 + size t) =
  match t with
  | L -> ()
  | N (l,y,r) -> if x <= y then insert_size x l else insert_size x r

let rec insert_height (x:int) (t:bst)
: Lemma (height (insert x t) <= 1 + height t)
=
  match t with
  | L -> ()
  | N (l,y,r) -> if x <= y then insert_height x l else insert_height x r

let rec insert_mem (x:int) (t:bst) : Lemma (member x (insert x t)) =
  match t with
  | L -> ()
  | N (l,y,r) -> if x <= y then insert_mem x l else insert_mem x r

(* ¿Puede demostrar también que:
     height t <= height (insert x t)
   ? ¿Cuál es la forma "más fácil" de hacerlo? *)

let rec insert_height' (x:int) (t:bst)
: Lemma (height t <= height (insert x t))
=
  match t with
  | L -> ()
  | N (l,y,r) -> if x <= y then insert_height' x l else insert_height' x r

let rec extract_min (t: bst{N? t}) : int & bst =
  match t with
  | N (L, x, r) -> (x, r)
  | N (l, x, r) ->
    let (y,l') = extract_min l in
    (y, N (l', x, r))

let delete_root (t: bst) : Pure bst (requires N? t) (ensures fun _ -> True) =
  match t with
  | N (l, _, L) -> l
  | N (l, _, r) ->
    let (x, r') = extract_min r in
    N (l, x, r')

let rec delete (x: int) (t: bst) : bst =
  match t with
  | L -> L
  | N (l, y, r) ->
    if x < y then N (delete x l, y, r)
    else if x > y then N (l, y, delete x r)
    else delete_root t

let rec extract_min_size (t: bst{N? t}) : Lemma (size (snd (extract_min t)) == size t - 1) =
  match t with
  | N (L,x,r) -> ()
  | N (l,x,r) -> extract_min_size l

(* Un poco más difícil. Require un lema auxiliar sobre extract_min:
declárelo y demuéstrelo. Si le parece conveniente, puede modificar
las definiciones de delete, delete_root y extract_min. *)
let rec delete_size (x:int) (t:bst) : Lemma (delete x t == t \/ size (delete x t) == size t - 1) =
  match t with
  | L -> ()
  | N (l,y,r) -> (
    if x = y then (
      if r = L then () else extract_min_size r
    )
    else if x < y then
      delete_size x l
    else if y < x then
      delete_size x r
  )

(* Versión más fuerte del lema anterior. *)
let rec delete_size_mem (x:int) (t:bst)
: Lemma (requires member x t)
        (ensures size (delete x t) == size t - 1)
= 
  match t with
  | N (l,y,r) -> (
    if x = y then (
      if r = L then () else extract_min_size r
    )
    else if x < y then
      delete_size_mem x l
    else
      delete_size_mem x r
  )

let len_append (xs ys : list int) : Lemma (length (xs @ ys) == length xs + length ys)
=
  ()

let rec to_list_length (t:bst) : Lemma (length (to_list t) == size t) =
  match t with
  | L -> ()
  | N (l,x,r) -> (
    to_list_length l;
    to_list_length r;
    len_append (to_list l) [x]
  )

(* Contestar en texto (sin intentar formalizar):
    ¿Es cierto que `member x (insert y (insert x t))`? ¿Cómo se puede probar?
    ¿Es cierto que `delete x (insert x t) == t`?
*)

(*
  1- member x (insert y (insert x t))
  Se podría probar con un lema auxiliar: member x t => member x (insert y t)
  Probaría que la inserción de elementos no borra elementos ya existentes

  2- delete x (insert x t) == t
  Es válido si (not (member x t)). Porque en ese caso, x queda en una
  hoja y el delete no modificará la estructura del árbol.
  En otro caso, como x puede ser un nodo con hijos, al borrarlo cambiará
  la estructura del árbol y una comparación como == resultará falsa.
*)