module Clase9.Eff

#set-options "--warn_error -272"

open FStar.IO
open FStar.All

let divide (x y : int)
: Exn int (requires y <> 0) (ensures fun _ -> True)
= x / y

exception DivZero

(* Lanzar una excepción. *)
let test (#a:Type) () : Exn a (requires True) (ensures fun r -> E? r) =
  raise DivZero;
  let x = divide 1 0 in
  assert False

(* Las excepciones pueden capturarse y relanzarse. *)

(* Escriba una versión "segura" de divide y dele una
especificación que garantice que el resultado
es la división de x e y (cuando y no es cero), y que lanza la excepción
DivZero si y=0. La precondición debe ser True. *)
let divide' (x y : int)
: Exn int (requires True)
          (ensures fun (r : result int) -> if y = 0 then r == E DivZero else V? r) // True)
= if y = 0 then raise DivZero;
  x / y

(* Las excepciones pueden capturarse (pero F* no soporta dar buenas especificaciones...
es simplemente algo que falta en la librería estándar, pero puede hacerse). *)
(* ML x = All x (fun _ -> True) (fun _ _ _ -> True) *)
let test_catch () : ML int =
  try
    divide' 1 0
  with
  | DivZero -> 0
  | _ -> 42 (* imposible, pero por la falta de especificación tenemos que escribir este caso *)

(* Versión pura de gcd *)
let rec gcd (x y : nat) : Tot nat (decreases %[y; x])  =
  //admit(); // borrar, demostrar terminación (puede restringir dominio)
  if y = 0 then x
  else if x < y then gcd y x
  else gcd y (x%y)

(* Una caché para gcd *)
let cache_elem_t = (x:nat & y:nat & z:nat{z == gcd x y})
let cache : ref (list cache_elem_t) = alloc []

(* Buscar en la caché. Para demostrar que el resultado es correcto, agregue
un refinamiento a cache_elem_t. Puede usar tuplas dependientes, o tuplas normales. *)
let find_in_cache (x y : nat) : ML (option (r:nat{r == gcd x y})) =
  let rec aux (xs : list cache_elem_t) : ML (option (r:nat{r == gcd x y})) =
    match xs with
    | [] -> None
    | (Mkdtuple3 x' y' z')::xs' ->
      if (x',y') = (x,y) then Some z' else aux xs'
  in
  aux !cache (* !cache lee la referencia *)

(* Versión memoizada, garantizando que el resultado es igual a la versión pura. *)
let memo_gcd (x y : nat) : ML (r:nat{r == gcd x y}) =
  match find_in_cache x y with
  | Some r -> r
  | None ->
    let r = gcd x y in
    cache := (Mkdtuple3 x y r ) :: !cache;
    r

exception Neg

let rec go () : ML _ =
  begin try
    let x = input_int () in
    let y = input_int () in
    (* Si alguno es negativo, lance una excepción. *)
    let _ = if x < 0 || y < 0 then raise Neg in
    let r = memo_gcd x y in (* cambiar por memo_gcd *)
    assert (r == gcd x y);
    print_string ("gcd = " ^ string_of_int r ^ "\n")
  with
  | _ ->
    print_string "Ups! Intentalo de nuevo.\n"
  end;
  go ()

let main () : ML unit =
  go ()
