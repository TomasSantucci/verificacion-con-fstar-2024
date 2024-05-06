module Clase5.Listas

open FStar.List.Tot

val sum_int : list int -> int
let rec sum_int xs =
  match xs with
 | [] -> 0
 | x::xs' -> x + sum_int xs'

(* Demuestre que sum_int "distribuye" sobre la concatenación de listas. *)
let rec sum_append (l1 l2 : list int)
  : Lemma (sum_int (l1 @ l2) == sum_int l1 + sum_int l2)
  =
  match l1 with
  | [] -> ()
  | x::xs -> (
    sum_append xs l2
  )

(* Idem para length, definida en la librería de F*. *)
let len_append (l1 l2 : list int)
  : Lemma (length (l1 @ l2) == length l1 + length l2)
  = ()

let rec snoc (xs : list int) (x : int) : list int =
  match xs with
  | [] -> [x]
  | y::ys -> y :: snoc ys x

(* unit-tests *)
let _ = assert (snoc [1;2;3] 4 == [1;2;3;4])
let _ = assert (snoc [1;2;3] 5 == [1;2;3;5])

let rec rev_int (xs : list int) : list int =
  match xs with
  | [] -> []
  | x::xs' -> snoc (rev_int xs') x

let rec snoc_append (xs ys : list int) (y : int) : Lemma (snoc (xs@ys) y == xs @ (snoc ys y)) =
  match xs with
  | [] -> ()
  | x::xs' -> (
    snoc_append xs' ys y
  )

let rec rev_append_int (xs ys : list int)
  : Lemma (rev_int (xs @ ys) == rev_int ys @ rev_int xs) =
  match xs with
  | [] -> ()
  | x::xs' -> (
    rev_append_int xs' ys;
    snoc_append (rev_int ys) (rev_int xs') x
  )

let rec rev_aux (xs : list int) (x : int) : Lemma (rev_int (snoc xs x) == x::(rev_int xs)) =
  match xs with
  | [] -> ()
  | x'::xs' -> (
    rev_aux xs' x;

    assert(rev_int (snoc xs x) == rev_int (x'::snoc xs' x));
    assert(rev_int (x'::snoc xs' x) == snoc (rev_int (snoc xs' x)) x');
    assert(snoc (rev_int (snoc xs' x)) x' == snoc (x::(rev_int xs')) x'); //HI
    assert(snoc (x::(rev_int xs')) x' == x::(snoc (rev_int xs') x'));
    assert(x::(snoc (rev_int xs') x') == x::rev_int (x'::xs'))
  )

let rec rev_rev (xs : list int)
  : Lemma (rev_int (rev_int xs) == xs)
=
  match xs with
  | [] -> ()
  | x::[] -> ()
  | x::xs' -> (
    rev_rev xs';
    rev_aux (rev_int xs') x
  )

let rev_injective (xs ys : list int)
  : Lemma (requires rev_int xs == rev_int ys) (ensures xs == ys)
=
  assert(rev_int xs == rev_int ys);
  assert(rev_int (rev_int xs) == rev_int (rev_int ys));
  rev_rev xs;
  rev_rev ys