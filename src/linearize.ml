open Syntax
open Transposition
open Type_checker
(* open Print *)

let empty_env_type = { env_nlt = Environnement.empty; env_lt = Environnement.empty; env_ft = Environnement.empty }

let rec find_list (env : var Environnement.t) (vs : var list) : var list =
  match vs with
    | [] -> []
    | v::q -> (try Environnement.find v env with Not_found -> failwith"a")::(find_list env q)

let rec is_in (vs : 'a list) (v : 'a) : bool =
  match vs with
    | [] -> false
    | t::_ when t = v -> true
    | _::q -> is_in q v

(* Checks if 'v' is well not free in e *)
let not_free (e : expr) (v : var) : bool =
  let rec aux e v =
  match e with
    | EVar w -> v != w
    | EDec (_, _, _, _, e1, e2) -> aux e1 v && aux e2 v
    | ENonLinUnpack (_, _, v', e') -> aux e' v && v != v'
    | ELinUnpack (_, _, _, e') -> aux e' v
    | EMultiValue (vs, _) -> not (is_in vs v)
    | ETuple vs -> not (is_in vs v)
    | ENonLinBinOp (v1, _, v2) -> v != v1 && v != v2
    | ENonLinUnOp (_, v') -> v != v'
    | EFunCall (_, vs, _) -> not (is_in vs v)
    | Drop e' -> aux e' v
    | _ -> true
  in let b = aux e v in
  if not b then failwith("try to unpack " ^ v ^ " which doesn't appears after")
  else b

(* Checks if variables in 'vs' are distincts *)
let rec distinct (vs : 'a list) : bool =
  match vs with
    | [] -> true
    | t::q when not (is_in q t) -> (distinct q)
    | _ -> failwith"try to linearize a list of variable which isn't distinct"

(* Returns the commons variables of 'vs1' and 'vs2' *)
let rec intersection (vs1 : 'a list) (vs2 : 'a list) : 'a list =
  match vs1 with
    | [] -> []
    | t::q when is_in vs2 t -> t::(intersection q vs2)
    | _::q -> intersection q vs2

(* The two following functions are used to create the expression with all the dup(...) in the LET rule *)
let rec duplication (env1 : var Environnement.t) (env2 : var Environnement.t) (vs1 : var list) (vs2 : var list) (ws : var list) (ws' : var list) (ts : value_type list) : var Environnement.t * var Environnement.t * expr =
  match vs1, vs2, ws, ws', ts with
    | [], [], [], [], [] -> env1, env2, EMultiValue ([], [])
    | v1::q1, v2::q2, v3::q3, v4::q4, t::q ->
        let env1 = Environnement.add v3 v1 env1 in
        let env2 = Environnement.add v3 v2 env2 in
        let env1, env2, e' = duplication env1 env2 q1 q2 q3 q4 q in
        env1, env2, EDec ([], [], [v1; v2], [t; t], Dup v4, e')
    | _ -> failwith"weird"

let rec fill (e1 : expr) (e2 : expr) : expr =
  match e1 with
    | EMultiValue ([], []) -> e2
    | EDec ([], [], lvs, lts, e1', e2') ->
        EDec ([], [], lvs, lts, e1', fill e2' e2)
    | _ -> failwith"weird"

let rec add_variable_list (env : 'a Environnement.t) (vs : 'a list) (vs' : 'a list) : 'a Environnement.t =
  match vs, vs' with
    | [], [] -> env
    | v1::q1, v2::q2 -> add_variable_list (Environnement.add v1 v2 env) q1 q2
    | _ -> failwith"weird"

(* Linearizes an expression *)
let rec linearize (env : var Environnement.t) (env_t : environnementTypes) (e : expr) : expr =
  match e with
    | ENonLinLiteral _ ->
        let v, v' = two_fresh_var [Real; Real] in
        let e' = EDec ([v], [Real], [], [], e, EMultiValue ([v], [v'])) in
        EDec ([], [], [v'], [Real], ELinZero Real , e')
    | EVar v ->
        (try
          EMultiValue ([v], [try Environnement.find v env with Not_found -> failwith"b"])
        with
          Not_found -> failwith("variable " ^ v ^ " is linear"))
    | ENonLinBinOp (v1, OpTimes, v2) ->
        let _ = distinct [v1; v2] in
        let v, v' = two_fresh_var [Real; Real] in
        let e1 = EDec ([v], [Real], [], [], e, EMultiValue ([v], [v'])) in
        let v1', v2' = two_fresh_var [Real; Real] in
        let e2 = EDec ([], [], [v'], [Real], ELinAdd (v1', v2'), e1) in
        let e3 = EDec ([], [], [v1'], [Real], ELinMul (v1, try Environnement.find v2 env with Not_found -> failwith"c"), e2) in
        EDec ([], [], [v2'], [Real], ELinMul (v2, try Environnement.find v1 env with Not_found -> failwith"d"), e3)
    | ENonLinBinOp (v1, OpPlus, v2) ->
        let _ = distinct [v1; v2] in
        let v, v' = two_fresh_var [Real; Real] in
        let e' = EDec ([v], [Real], [], [], e, EMultiValue ([v], [v'])) in
        EDec ([], [], [v'], [Real], ELinAdd ((try Environnement.find v1 env with Not_found -> failwith"e"), try Environnement.find v2 env with Not_found -> failwith"f") , e')
    | ENonLinBinOp (v1, OpMinus, v2) ->
        let _ = distinct [v1; v2] in
        let v, v' = two_fresh_var [Real; Real] in
        let e' = EDec ([v], [Real], [], [], e, EMultiValue ([v], [v'])) in
        EDec ([], [], [v'], [Real], ELinAdd ((try Environnement.find v1 env with Not_found -> failwith"g"), try Environnement.find v2 env with Not_found -> failwith"h") , e')
    | ENonLinBinOp (v, OpDiv, v') ->
        let _ = distinct [v; v'] in
        let (v1, v2), (v3, v4), (v5, v6), (v7, v8), (v9, v10) = two_fresh_var [Real; Real], two_fresh_var [Real; Real], two_fresh_var [Real; Real], two_fresh_var [Real; Real], two_fresh_var [Real; Real] in
        let e1 = EDec ([], [], [v10], [Real], ELinMul (v9, v6) , EMultiValue ([v1], [v10])) in
        let e2 = EDec ([v9], [Real], [], [], ENonLinBinOp (v8, OpDiv, v7), e1) in
        let e3 = EDec ([v8], [Real], [], [], ENonLinLiteral 1., e2) in
        let e4 = EDec ([v7], [Real], [], [], ENonLinBinOp (v', OpTimes, v'), e3) in
        let e5 = EDec ([], [], [v6], [Real], ELinAdd (v2, v5), e4) in
        let e6 = EDec ([], [], [v5], [Real], ELinMul (v4, v3), e5) in
        let e7 = EDec ([v4], [Real], [], [], ENonLinLiteral (-1.), e6) in
        let e8 = EDec ([], [], [v3], [Real], ELinMul (v, try Environnement.find v' env with Not_found -> failwith"i"), e7) in
        let e9 = EDec ([], [], [v2], [Real], ELinMul (v', try Environnement.find v env with Not_found -> failwith"j"), e8) in
        EDec ([v1], [Real], [], [], e, e9)
    | ENonLinUnOp (OpSin, v) ->
        let (v1, v2), v3 = two_fresh_var [Real; Real], one_fresh_var [Real] in
        let e1 = EDec ([v1], [Real], [], [], e, EMultiValue ([v1], [v3])) in
        let e2 = EDec ([], [], [v3], [Real], ELinMul (v2, try Environnement.find v env with Not_found -> failwith"k"), e1) in
        EDec ([v2], [Real], [], [], ENonLinUnOp (OpCos, v), e2)
    | ENonLinUnOp (OpCos, v) ->
        let (v1, v2), (v3, v4), v5 = two_fresh_var [Real; Real], two_fresh_var [Real; Real], one_fresh_var [Real] in
        let e1 = EDec ([v1], [Real], [], [], e, EMultiValue ([v1], [v5])) in
        let e2 = EDec ([], [], [v5], [Real], ELinMul (v4, try Environnement.find v env with Not_found -> failwith"l"), e1) in
        let e3 = EDec ([v4], [Real], [], [], ENonLinBinOp (v3, OpTimes, v2), e2) in
        let e4 = EDec ([v3], [Real], [], [], ENonLinLiteral (-1.), e3) in
        EDec ([v2], [Real], [], [], ENonLinUnOp (OpSin, v), e4)
    | ENonLinUnOp (OpExp, v) ->
        let (v1, v2) = two_fresh_var [Real; Real] in
        let e1 = EDec ([], [], [v2], [Real], ELinMul (v1, try Environnement.find v env with Not_found -> failwith"m"), EMultiValue ([v1], [v2])) in
        EDec ([v1], [Real], [], [], ENonLinUnOp (OpExp, v), e1)
    | ETuple vs ->
        let _ = distinct vs in
        let vs' = find_list env vs in
        let ts = try type_list env_t vs with Not_found -> failwith"p" in
        let v1, v2 = two_fresh_var [Tuple ts; Tuple ts] in
        let e' = EDec ([v1], [Tuple ts], [], [], e, EMultiValue ([v1], [v2])) in
        EDec ([], [], [v2], [Tuple ts], ETuple vs', e')
    | EMultiValue (vs, []) ->
        let _ = distinct vs in
        let vs' = find_list env vs in
        EMultiValue (vs, vs')
    | EDec (vs, ts, _, _, e1, e2) ->
        let _ = distinct vs in
        let env_t = add_variable_types env_t vs [] ts [] in
        let vs1 = free_non_linear_variables env_t e1
        and vs2 = free_non_linear_variables env_t e2 in
        let ws = intersection vs1 vs2 in
        let ws' = find_list env ws in
        let ts' = try type_list env_t ws with Not_found -> failwith"q" in
        let vs1, vs2 = fresh_var ts', fresh_var ts' in
        let vs' = fresh_var ts in
        let env = add_variable_list env vs vs' in
        let env1, env2, e' = duplication env env vs1 vs2 ws ws' ts' in
        let e1' = linearize env1 env_t e1 in
        let e2' = linearize env2 env_t e2 in
        let e3 = EDec (vs, ts, vs', ts, e1', e2') in
        let e' = fill e' e3 in
        e'
    | ENonLinUnpack (vs, ts, v, e) ->
        let _ = not_free e v in
        let _ = distinct vs in
        let vs' = fresh_var ts in
        let env = add_variable_list env vs vs' in
        let env_t = add_variable_types env_t vs [] ts [] in
        let e' = linearize env env_t e in
        let v' = try Environnement.find v env with Not_found -> failwith"n" in
        ENonLinUnpack (vs, ts, v, ELinUnpack (vs', ts, v', e'))
    | EFunCall (f, vs, []) ->
        let _ = distinct vs in
        let f' = try Environnement.find f env with Not_found -> failwith"o" in
        let vs' = find_list env vs in
        EFunCall (f', vs, vs')
    | Drop e ->
        let e' = linearize env env_t e in
        Drop e'
    | _ -> failwith"Linearity in a non linear program"


(* Linearizes a program *)
let rec linearize_prog (env : var Environnement.t) (p : prog) : prog =
  match p with
    | [] -> []
    | (FunDec (f, vs, ts, [], [], e))::q ->
        let f' = fresh_fun f in
        let env = Environnement.add f f' env in
        let p' = linearize_prog env q in
        let env_t = add_variable_types empty_env_type vs [] ts [] in
        let vs' = fresh_var ts in
        let env = add_variable_list env vs vs' in
        let e' = linearize env env_t e in
        (FunDec (f', vs, ts, vs', ts, e'))::p'
    | _ -> failwith"Linearity in a non linear program"