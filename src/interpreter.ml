open Syntax

(* evaluation of non linear binary operation *)
let nlbinop (v1 : multivalue) (op : binop) (v2 : multivalue) : multivalue =
  match v1, v2 with
    | MultiValue ([Real f1], []), MultiValue ([Real f2], []) ->
      (match op with
        | OpPlus -> MultiValue ([Real (f1 +. f2)], [])
        | OpMinus -> MultiValue ([Real (f1 -. f2)], [])
        | OpTimes -> MultiValue ([Real (f1 *. f2)], [])
        | OpDiv -> MultiValue ([Real (f1 /. f2)], []))
    | _ -> failwith"binary operation between unauthorize types"

(* evaluation of non linear unary operation *)
let unop (v : multivalue) (op : unop) : multivalue =
  match v with
    | MultiValue ([Real f], []) ->
      (match op with
        | OpCos -> MultiValue([Real (cos f)], [])
        | OpSin -> MultiValue([Real (sin f)], [])
        | OpExp -> MultiValue([Real (exp f)], []))
    | _ -> failwith"unary operation on an unauthorized type"

(* evaluation of linear addition *)
let linadd (v1 : multivalue) (v2 : multivalue) : multivalue =
  let rec aux (x1 : value) (x2 : value) : value =
    match x1, x2 with
      | Real f1, Real f2 -> Real (f1 +. f2)
      | Tuple [], Tuple [] -> Tuple []
      | Tuple (x1::q1), Tuple (x2::q2) ->
        let x = aux (Tuple q1) (Tuple q2) in
        (match x with
          | Tuple xs -> Tuple ((aux x1 x2)::xs)
          | _ -> failwith"weird")
      | _ -> failwith"weird"
  in match v1, v2 with
    | MultiValue ([], [x1]), MultiValue ([], [x2]) ->
      MultiValue ([], [aux x1 x2])
    | _ -> failwith"binary operation between non authorize types"

(* evaluation of linear multiplication *)
let linmul (v1 : multivalue) (v2 : multivalue) : multivalue =
  match v1, v2 with
    | MultiValue ([Real f1], []), MultiValue ([], [Real f2]) ->
    MultiValue ([], [Real (f1 *. f2)])
    | _ -> failwith"binary operation between non authorize types"

(* evaluation of the linear zero *)
let rec zero (t : value_type) : value =
  match t with
    | Real -> Real 0.0
    | Tuple ([]) -> Tuple []
    | Tuple (t::q) -> 
      (match zero (Tuple q) with
        | Tuple z -> Tuple ((zero t)::z)
        | _ -> failwith"weird")

(* How to stock variables and their value or functions *)

let empty_environnement =
  { env_nlv = Environnement.empty; env_lv = Environnement.empty; env_f = Environnement.empty }

(* returns the value of the two list of variables *)  
let read_values (env : environnement) (nlvs : var list) (lvs : var list) : multivalue =
  let env_nlvs, env_lvs = env.env_nlv, env.env_lv in
  let rec aux (env_v : environnementVariables) (vs : var list) : value list =
    match vs with
      | [] -> []
      | a::b ->
        let x = Environnement.find a env_v in
        x :: (aux env_v b)
  in MultiValue (aux env_nlvs nlvs, aux env_lvs lvs)

 (* same for a tuple *) 
let read_tuple (env : environnement) (vs : var list) : multivalue =
  let rec aux (env_v : environnementVariables) (vs : var list) : value =
    match vs with
      | [] -> Tuple []
      | v::q ->
        let x = Environnement.find v env_v in
        (match aux env_v q with
          | Tuple xs ->
            Tuple (x::xs)
          | _ -> failwith"weird")
  in try
    MultiValue ([aux env.env_nlv vs], [])
  with
    Not_found -> MultiValue ([], [aux env.env_lv vs])

(* adds variables with their value in the environnement *) 
let add_variables (env : environnement) (nlvs : var list) (lvs : var list) (nlxs : value list) (lxs : value list) : environnement =
  let env_nlv, env_lv, env_f = env.env_nlv, env.env_lv, env.env_f in
  let rec aux vs xs env_var =
    match vs, xs with
      | [], [] -> env_var
      | [], _| _, [] -> failwith"type error"
      | a::b, c::d ->
        let env_var = Environnement.add a c env_var in
        aux b d env_var
  in { env_nlv = aux nlvs nlxs env_nlv ; env_lv = aux lvs lxs env_lv; env_f = env_f}

(* returns the value of a variable stored in the environnement *)
let find (env : environnement) (v : var) : multivalue =
  try
    MultiValue ([Environnement.find v env.env_nlv], [])
  with
    Not_found -> MultiValue ([], [Environnement.find v env.env_lv])

(* the main function, it returns the result of an expression *)
let rec execute (env : environnement) (e : expr) : multivalue =
  match e with
    | EMultiValue (nlvs, lvs) -> read_values env nlvs lvs
    | ELet (nlvs, _, lvs, _, e1, e2) ->
      let MultiValue (nlxs, lxs) = execute env e1 in
      let env = add_variables env nlvs lvs nlxs lxs
      in execute env e2
    | EFunCall (f, nlv1s, lv1s) -> 
      let nlv2s, lv2s, e = Environnement.find f env.env_f in
      let MultiValue (nlxs, lxs) = read_values env nlv1s lv1s in
      let env = add_variables env nlv2s lv2s nlxs lxs in
      execute env e
    | ENonLinLiteral f -> MultiValue ([Real f], [])
    | EVar v ->
      find env v
    | ENonLinBinOp (v1, op, v2) -> 
      let x1, x2 = find env v1, find env v2 in
      nlbinop x1 op x2
    | ENonLinUnOp (op, v) ->
      let x = find env v in
      unop x op
    | ELinAdd (v1, v2) ->
      let x1, x2 = find env v1, find env v2 in
      linadd x1 x2
    | ELinMul (v1, v2) ->
      let x1, x2 = find env v1, find env v2 in
      linmul x1 x2
    | ELinZero t ->
      MultiValue ([], [zero t])
    | Dup v -> 
      (match read_values env [] [v] with
        | MultiValue ([], [x]) ->
            MultiValue ([], [x; x])
        | _ -> failwith"type error")
    | Drop _ -> MultiValue ([], [])
    | ETuple vs ->
      read_tuple env vs
    | ENonLinUnpack (vs, _, v, e') ->
      (match find env v with
        | MultiValue ([Tuple xs], []) -> 
          let env = add_variables env vs [] xs [] in
          execute env e'
        | _ -> failwith"try to unpack a tuple with the wrong number of variables")
    | ELinUnpack (vs, _, v, e') ->
      (match find env v with
        | MultiValue ([], [Tuple xs]) -> 
          let env = add_variables env [] vs [] xs in
          execute env e'
        | _ -> failwith"try to unpack a tuple with the wrong number of variables")

(* returns the result of a programm *)
let rec interpret (env : environnement) (p : prog) =
  match p with
    | [] -> failwith"empty program"
    | [FunDec ("main", _, _, _, _, e)] ->
      execute env e
    | (FunDec (f, nlvs, _, lvs, _, e))::q ->
      let env_f = Environnement.add f (nlvs, lvs, e) env.env_f
      in interpret {env_nlv = env.env_nlv; env_lv = env.env_lv; env_f = env_f } q
