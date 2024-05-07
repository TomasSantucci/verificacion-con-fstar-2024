module Clase7.Imp

open FStar.Mul

type var = string

type expr =
  | Var   : var -> expr
  | Const : int -> expr
  | Plus  : expr -> expr -> expr
  | Minus : expr -> expr -> expr
  | Times : expr -> expr -> expr
  | Eq    : expr -> expr -> expr

type stmt =
  | Assign : var -> expr -> stmt
  | IfZ    : expr -> stmt -> stmt -> stmt
  | Seq    : stmt -> stmt -> stmt
  | Skip   : stmt
  | While  : expr -> stmt -> stmt

type state = var -> int

let rec eval_expr (s : state) (e : expr) : int =
  match e with
  | Var x -> s x
  | Const n -> n
  | Plus  e1 e2 -> eval_expr s e1 + eval_expr s e2
  | Minus e1 e2 -> eval_expr s e1 - eval_expr s e2
  | Times e1 e2 -> eval_expr s e1 * eval_expr s e2
  | Eq e1 e2 -> if eval_expr s e1 = eval_expr s e2 then 0 else 1

let override (#a:eqtype) (#b:Type) (f : a -> b) (x:a) (y:b) : a -> b =
  fun z -> if z = x then y else f z

(* Relación de evaluación big step. *)
noeq
type runsto : (p:stmt) -> (s0:state) -> (s1:state) -> Type0 =
  | R_Skip : s:state -> runsto Skip s s
  | R_Assign : s:state -> #x:var -> #e:expr -> runsto (Assign x e) s (override s x (eval_expr s e))

  | R_Seq :
    #p:stmt -> #q:stmt ->
    #s:state -> #t:state -> #u:state ->
    runsto p s t -> runsto q t u -> runsto (Seq p q) s u

  | R_IfZ_True :
    #c:expr -> #t:stmt -> #e:stmt ->
    #s:state -> #s':state -> runsto t s s' ->
    squash (eval_expr s c == 0) ->
    runsto (IfZ c t e) s s'

  | R_IfZ_False :
    #c:expr -> #t:stmt -> #e:stmt ->
    #s:state -> #s':state -> runsto e s s' ->
    squash (eval_expr s c <> 0) ->
    runsto (IfZ c t e) s s'

  | R_While_True :
    #c:expr -> #b:stmt -> #s:state -> #s':state -> #s'':state ->
    runsto b s s' ->
    squash (eval_expr s c = 0) ->
    runsto (While c b) s' s'' ->
    runsto (While c b) s s''

  | R_While_False :
    #c:expr -> #b:stmt -> #s:state ->
    squash (eval_expr s c <> 0) ->
    runsto (While c b) s s

// Demostrar que esta regla es admisible, es decir, que
// podemos "asumir" que la tenemos para demostrar, pero no
// necesitamos analizarla cuando destruímos una prueba:
//
// | R_While :
//   #c:expr -> #b:stmt ->
//   #s:state -> #s':state ->
//   runsto (IfZ c (Seq b (While c b)) Skip) s s' ->
//   runsto (While c b) s s'
let r_while (#c:expr) (#b:stmt) (#s #s' : state) (pf : runsto (IfZ c (Seq b (While c b)) Skip) s s')
  : runsto (While c b) s s'
=
  match pf with
  | R_IfZ_True rseq sq -> (
    let R_Seq rb rw = rseq in
    R_While_True rb sq rw
  )
  | R_IfZ_False rsk _ -> (
    R_While_False ()
  )

type cond = state -> bool

noeq
type hoare : (pre:cond) -> (p:stmt) -> (post:cond) -> Type0 =
  | H_Skip : pre:cond -> hoare pre Skip pre // {P} Skip {P}
  | H_Seq :
    #p:stmt -> #q:stmt ->
    #pre:cond -> #mid:cond -> #post:cond ->
    hoare pre p mid -> hoare mid q post ->
    hoare pre (Seq p q) post  // {pre} p {mid} /\ {mid} q {post}    ==>    {pre} p;q {post}
  | H_Assign :
    #x:var -> #e:expr ->
    #post:cond ->
    hoare (fun (s:state) -> post (override s x (eval_expr s e))) (Assign x e) post
  | H_If :
    #pre:cond -> #post:cond ->
    #c:expr -> #t:stmt -> #e:stmt ->
    hoare (fun (s:state) -> pre s && (eval_expr s c = 0)) t post ->
    hoare (fun (s:state) -> pre s && (eval_expr s c <> 0)) e post ->
    hoare pre (IfZ c t e) post
  | H_While :
    #inv:cond ->
    #c:expr -> #b:stmt ->
    hoare (fun (s:state) -> inv s && (eval_expr s c = 0)) b inv ->
    hoare inv (While c b) (fun (s:state) -> inv s && (eval_expr s c <> 0))

let rec hoare_ok (p:stmt) (pre:cond) (post:cond) (pf : hoare pre p post)
                 (s0 s1 : state) (e_pf : runsto p s0 s1)
  : Lemma (requires pre s0)
          (ensures  post s1)
=
  match pf with
  | H_Skip pre' -> ()
  | H_Seq #s #q #pre' #mid #post' pmid qmid -> (
    match e_pf with
    | R_Seq #_ #_ #s0' #s1' #s2' r1 r2 -> (
      hoare_ok s pre' mid pmid s0' s1' r1;
      hoare_ok q mid post' qmid s1' s2' r2
    )
  )
  | H_Assign #x #e #post' -> ()
  | H_If #_ #_ #c #t #e pt pe -> (
    match e_pf with
    | R_IfZ_True r _ ->
      hoare_ok t (fun (s:state) -> pre s && (eval_expr s c = 0)) post pt s0 s1 r
    | R_IfZ_False r _ ->
      hoare_ok e (fun (s:state) -> pre s && (eval_expr s c <> 0)) post pe s0 s1 r
  )
  | H_While #inv #c #b pb -> (
    match e_pf with
    | R_While_True #_ #_ #s0' #s1' #s2' rb _ rw -> (
      hoare_ok b (fun (s:state) -> inv s && (eval_expr s c = 0)) inv pb s0' s1' rb;
      hoare_ok (While c b) inv (fun (s:state) -> inv s && (eval_expr s c <> 0)) pf s1' s2' rw
    )
    | R_While_False _ -> ()
  )

let st0 : state = fun _ -> 0

let test1 : hoare (fun _ -> true) (Assign "x" (Const 1)) (fun s -> s "x" = 1) =
  H_Assign
