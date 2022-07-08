open Syntax
open Transposition

let type_size = 3
let _ = Random.self_init ()

(* Checks if it exists a variable with the type 't' in 'env' *)
let is_type_in (env : value_type Environnement.t) (t : value_type) : bool =
  let l = Environnement.bindings env in
  let rec aux (l : (var * value_type) list) : bool =
    match l with
      | [] -> false
      | (_, t')::_ when t = t' -> true
      | _::q -> aux q
  in aux l

let is_multivaluetype_in (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (mvt : multivalue_type_hl) : bool =
  let l = Environnement.bindings envf in
  let rec aux (l : (var * ((value_type list) * multivalue_type_hl)) list) : bool =
    match l with
      | [] -> false
      | (_, (_, mvt'))::_ when mvt = mvt' -> true
      | _::q -> aux q
  in aux l

(* Returns the list a of the variables with the desired type *)
let rec good_type_list (l : (var * value_type) list) (t : value_type) : var list =
  match l with
    | [] -> []
    | (v, t')::q when t = t' -> v::(good_type_list q t)
    | _::q -> good_type_list q t

let rec good_multivaluetype_list (l : (var * ((value_type list) * multivalue_type_hl)) list) (mvt : multivalue_type_hl) : var list =
  match l with
    | [] -> []
    | (f, (_, mvt'))::q when mvt = mvt' -> f::(good_multivaluetype_list q mvt)
    | _::q -> good_multivaluetype_list q mvt

(* Returns randomly a variable with the desired type of 'env' *)
let random_var (env : value_type Environnement.t) (t : value_type) : var =
  let l = Environnement.bindings env in
  let l = good_type_list l t in
  let p = List.length l in
  let p = Random.int p in
  let v = List.nth l p in v

(* Same for a function *)
let random_fun (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (mvt : multivalue_type_hl) : var =
  let l = Environnement.bindings envf in
  let l = good_multivaluetype_list l mvt in
  let p = List.length l in
  let p = Random.int p in
  let f = List.nth l p in f

(* Creates a list of 'size' int the sum of which is 'n' *)
let rec random_int_list (n : int) (size : int) : int list =
    match size with
      | 0 -> []
      | 1 -> [n]
      | _ ->
          let size' = size / 2 in
          let n' = Random.int (n + 1) in
          (random_int_list n' size') @ (random_int_list (n - n') (size - size'))

(* Makes a list of 'n' Real *)
let rec real_list (n : int) : value_type list =
  match n with
    | 0 -> []
    | _ -> Real::(real_list (n - 1))

(* Creates a radom type of size 'n' *)    
let rec random_type (n : int) : value_type =
  match n with
    | 0 -> Real
    | _ ->
        let size = (Random.int n) + 1 in
        let ns = random_int_list (n - 1) size in
        Tuple (random_type_list ns)

and random_type_list (ns : int list) : value_type list =
  match  ns with
    | [n] -> [random_type n]
    | [] -> [Real]
    | _ -> real_list (List.length ns)
  (* match ns with
    | [] -> [Real]
    | [n] -> [random_type n]
    | n::nq ->
        (random_type n)::(random_type_list nq) *)

let random_binop () : binop =
  let p = Random.int 4 in
  match p with
    | 0 -> OpPlus
    | 1 -> OpMinus
    | 2 -> OpTimes
    | 3 -> OpDiv
    | _ -> failwith"weird"

let random_unop () : unop =
  let p = Random.int 3 in
  match p with
    | 0 -> OpCos
    | 1 -> OpSin
    | 2 -> OpExp
    | _ -> failwith"weird"

type expr_hl_type = T of value_type | MVT of value_type list

let rec add_list (env : 'a Environnement.t) (vs : var list) (ts : 'a list) : 'a Environnement.t =
  match vs, ts with
    | [], [] -> env
    | v::vq, t::tq ->
        let env = Environnement.add v t env in
        add_list env vq tq
    | _ -> failwith"weird"

(* Generates a random expression of size 'n' with the type 't'. 'type_size' is the maximal size of the types in the expression. *)
let rec generate (env : value_type Environnement.t) (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (t : expr_hl_type) (n : int) (type_size : int) : expr_hl =
  let m = Random.int 13 in
  match n, m, t with
    | _, 0, T t' when is_type_in env t' ->
        let v = random_var env t' in
        HLVar v
    | _, 1,T Real -> HLLiteral (Random.float 10.)
    | n, m, T Real when n >= 1 && (m = 2 || m = 9 || m = 10) ->
        let op = random_binop () in
        let n' = Random.int n in
        let e1 = generate env envf (T Real) n' type_size in
        let e2 = generate env envf (T Real) (n - 1 - n') type_size in
        HLBinOp (e1, op, e2)
    | n, m, T Real when n >= 1  && (m = 3 || m = 11 || m = 12) ->
        let op = random_unop () in
        let e = generate env envf (T Real) (n - 1) type_size in
        HLUnOp (op, e)
    | _, 4, T (Tuple ts) ->
        let size = List.length ts in
        let n' = max 0 (n - 1) in
        let ns = random_int_list n' size in
        let es = random_expr_list env envf ns ts in
        HLTuple es
    | _, 5, MVT ts ->
        let size = List.length ts in
        let n' = max 0 (n - 1) in
        let ns = random_int_list n' size in
        let es = random_expr_list env envf ns ts in
        HLMultiValue es
    | n, 6, _ when n >= 1 ->
        let n' = (Random.int type_size) + 1 in
        let size = Random.int (n' + 1) in
        let ns = random_int_list n' size in
        let ts' = random_type_list ns in
        let vs = fresh_var ts' in
        let e1 = generate env envf (MVT ts') n' type_size in
        let env = add_list env vs ts' in
        let e2 = generate env envf t (n - 1 - n') type_size in
        HLLet (vs, ts', e1, e2)
    | n, 7, _ when n >= 1 ->
        let n' = (Random.int type_size) + 1 in
        let size = Random.int (n' + 1) in
        let ns = random_int_list n' size in
        let ts' = random_type_list ns in
        let vs = fresh_var ts' in
        let e1 = generate env envf (T (Tuple ts')) n' type_size in
        let env = add_list env vs ts' in
        let e2 = generate env envf t (n - 1 - n') type_size in
        HLUnpack (vs, ts', e1, e2)
    | n, 8, MVT ts when n >= 1 ->
        if (is_multivaluetype_in envf (HLMultiValueType ts)) then
        (let f = random_fun envf (HLMultiValueType ts) in
        let ts, _ = Environnement.find f envf in
        let n' = Random.int n in
        let size = List.length ts in
        let ns = random_int_list n' size in
        let es = random_expr_list env envf ns ts in
        HLFunCall (f, es))
        else generate env envf t n type_size
    | _ -> generate env envf t n type_size

and random_expr_list (env : value_type Environnement.t) (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (ns : int list) (ts : value_type list) : expr_hl list =
  match ns, ts with
    | [], [] -> []
    | n::nq, t::tq ->
        let e = generate env envf (T t) n type_size in
        let es = random_expr_list env envf nq tq in
        e::es
    | _ -> failwith"weird"

let rec generate_prog (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (nb_f : int) (f_size : int) (type_size : int) : prog_hl =
  match nb_f with
    | 0 -> []
    | _ ->
      let f = "f" ^ (string_of_int (fresh_int ())) in
      let size = Random.int (type_size + 1) in
      let ns = random_int_list type_size size in
      let ts = random_type_list ns in
      let vs = fresh_var ts in
      let size' = Random.int (type_size + 1) in
      let ns' = random_int_list type_size size' in
      let ts' = random_type_list ns' in
      let env = add_list Environnement.empty vs ts in
      let e = generate env envf (MVT ts') f_size type_size in
      let envf = Environnement.add f (ts, HLMultiValueType ts') envf in
      (HLFunDec (f, vs, ts, e))::(generate_prog envf (nb_f -1) f_size type_size)