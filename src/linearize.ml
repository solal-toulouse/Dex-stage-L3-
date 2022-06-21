open Syntax
open Transposition
open Type_checker
(* open Print *)

let empty_env_type = { env_nlt = Environnement.empty; env_lt = Environnement.empty; env_ft = Environnement.empty }

let linear_var (env : (var list) Environnement.t) (v : var) : (var list) Environnement.t * var =
  let vs = Environnement.find v env in
  match vs with
    | [] -> failwith("No linear variable for " ^ v)
    | v'::q ->
        let env = Environnement.add v q env in
        env, v'

let rec find_list (env : (var list) Environnement.t) (vs : var list) : var list =
  match vs with
    | [] -> []
    | v::q ->
        let env, v' = try linear_var env v with Not_found -> failwith"a" in
        v'::(find_list env q)

let rec is_in (vs : 'a list) (v : 'a) : bool =
  match vs with
    | [] -> false
    | t::_ when t = v -> true
    | _::q -> is_in q v

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
        env1, env2, ELet ([], [], [v1; v2], [t; t], Dup v4, e')
    | _ -> failwith"weird"

let rec fill (e1 : expr) (e2 : expr) : expr =
  match e1 with
    | EMultiValue ([], []) -> e2
    | ELet ([], [], lvs, lts, e1', e2') ->
        ELet ([], [], lvs, lts, e1', fill e2' e2)
    | _ -> failwith"weird"

let rec add_variable_list (env : ('a list) Environnement.t) (vs : 'a list) (vs' : 'a list list) : ('a list) Environnement.t =
  match vs, vs' with
    | [], [] -> env
    | v1::q1, v2::q2 -> add_variable_list (Environnement.add v1 v2 env) q1 q2
    | _ -> failwith"weird"

(* Returns 'let v = v1*v2' + v2*v1' in *)
let derivation_mul (env : (var list) Environnement.t) (e : expr) (v1 : var) (v2 : var) (v : var) : (var list) Environnement.t * expr =
  let v1', v2' = two_fresh_var [Real; Real] in
  let e1 = ELet ([], [], [v], [Real], ELinAdd (v1', v2'), e) in
  let env, v1'' = try linear_var env v1 with Not_found -> failwith"c" in
  let env, v2'' = try linear_var env v2 with Not_found -> failwith"d" in
  let e2 = ELet ([], [], [v1'], [Real], ELinMul (v1, v2''), e1) in
  env, ELet ([], [], [v2'], [Real], ELinMul (v2, v1''), e2)

let derivation_add (env : (var list) Environnement.t) (e : expr) (v1 : var) (v2 : var) (v : var) : (var list) Environnement.t * expr =
  let env, v1' = try linear_var env v1 with Not_found -> failwith"e" in
  let env, v2' = try linear_var env v2 with Not_found -> failwith"f" in
  env, ELet ([], [], [v], [Real], ELinAdd (v1', v2') , e)

let derivation_min (env : (var list) Environnement.t) (e : expr) (v1 : var) (v2 : var) (v : var) : (var list) Environnement.t * expr =
  let env, v1' = try linear_var env v1 with Not_found -> failwith"g" in
  let env, v2' = try linear_var env v2 with Not_found -> failwith"h" in
  let v3, v4 = two_fresh_var [Real; Real] in
  let e1 = ELet ([], [], [v], [Real], ELinAdd (v1', v3), e) in
  let e2 = ELet ([], [], [v3], [Real], ELinMul (v4, v2'), e1) in
  env, ELet ([v4], [Real], [], [], ENonLinLiteral (-1.), e2)

let derivation_div (env : (var list) Environnement.t) (e : expr) (v1 : var) (v2 : var) (v : var) : (var list) Environnement.t * expr =
  let env, v1' = try linear_var env v1 with Not_found -> failwith"i" in
  let env, v2' = try linear_var env v2 with Not_found -> failwith"j" in
  let (v3, v4), (v5, v6), (v7, v8), (v9, v10) = two_fresh_var [Real; Real], two_fresh_var [Real; Real], two_fresh_var [Real; Real], two_fresh_var [Real; Real] in
  let e1 = ELet ([], [], [v], [Real], ELinMul (v3, v4) , e) in
  let e2 = ELet ([v3], [Real], [], [], ENonLinBinOp (v5, OpDiv, v6), e1) in
  let e3 = ELet ([v5], [Real], [], [], ENonLinLiteral 1., e2) in
  let e4 = ELet ([v6], [Real], [], [], ENonLinBinOp (v2, OpTimes, v2), e3) in
  let e5 = ELet ([], [], [v4], [Real], ELinAdd (v7, v8), e4) in
  let e6 = ELet ([], [], [v7], [Real], ELinMul (v9, v10), e5) in
  let e7 = ELet ([v9], [Real], [], [], ENonLinLiteral (-1.), e6) in
  let e8 = ELet ([], [], [v10], [Real], ELinMul (v1, v2'), e7) in
  env, ELet ([], [], [v8], [Real], ELinMul (v2, v1'), e8)

let derivation_sin (env : (var list) Environnement.t) (e : expr) (v1 : var) (v : var) : (var list) Environnement.t * expr =
  let env, v1' = try linear_var env v1 with Not_found -> failwith"k" in
  let v2 = one_fresh_var [Real] in
  let e1 = ELet ([], [], [v], [Real], ELinMul (v2, v1'), e) in
  env, ELet ([v2], [Real], [], [], ENonLinUnOp (OpCos, v1), e1)

let derivation_cos (env : (var list) Environnement.t) (e : expr) (v1 : var) (v : var) : (var list) Environnement.t * expr =
  let env, v1' = try linear_var env v1 with Not_found -> failwith"l" in
  let (v2, v3), v4 = two_fresh_var [Real; Real], one_fresh_var [Real] in
  let e1 = ELet ([], [], [v], [Real], ELinMul (v4, v1'), e) in
  let e2 = ELet ([v4], [Real], [], [], ENonLinBinOp (v3, OpTimes, v2), e1) in
  let e3 = ELet ([v3], [Real], [], [], ENonLinLiteral (-1.), e2) in
  env, ELet ([v2], [Real], [], [], ENonLinUnOp (OpSin, v1), e3)

let derivation_exp (env : (var list) Environnement.t) (e : expr) (v1 : var) (v : var) : (var list) Environnement.t * expr =
  let env, v1' = try linear_var env v with Not_found -> failwith"m" in
  let v2 = one_fresh_var [Real] in
  let e1 = ELet ([], [], [v], [Real], ELinMul (v2, v1'), e) in
  env, ELet ([v2], [Real], [], [], ENonLinUnOp (OpExp, v1), e1)

let rec repeat_list (n : int) (l : 'a list) : 'a list =
  match n with
    | 0 -> []
    | n -> l @ (repeat_list (n-1) l)

let rec nb_occurence_list (vs : var list) (v : var) =
  match vs with
    | [] -> 0
    | v'::vq when v = v' ->
        1 + (nb_occurence_list vq v)
    | _::vq -> nb_occurence_list vq v

let rec nb_occurence (e : expr) (v : var) : int =
  match e with
    | EVar v' ->
        (if v = v' then 1 else 0)
    | ENonLinBinOp (v1, _, v2) ->
        (if v = v1 then 1 else 0) + (if v = v2 then 1 else 0)
    | ENonLinUnOp (_, v') ->
        (if v = v' then 1 else 0)
    | ETuple vs ->
        nb_occurence_list vs v
    | EMultiValue (vs, _) ->
        nb_occurence_list vs v
    | ELet (_, _, _, _, e1, e2) ->
        nb_occurence e1 v + nb_occurence e2 v
    | ENonLinUnpack (_, _, v', e') ->
        (if v = v' then 1 else 0) + nb_occurence e' v
    | EFunCall (_, vs, _) ->
        nb_occurence_list vs v
    | Dup v' ->
        (if v = v' then 1 else 0)
    | Drop e' ->
        nb_occurence e' v
    | _ -> 0

let rec fresh_var_list (e : expr) (vs : var list) (ts : value_type list) : var list list= 
  match vs, ts with
    | [], [] -> []
    | v::vq, t::tq ->
        let n = nb_occurence e v in
        let vs' = fresh_var (repeat_list n [t]) in
        vs'::(fresh_var_list e vq tq)
    | _ -> failwith"weird"

(* Defines each variable in 'vss' with some 'Dup'. 'vs' is the list of the variables initially defined by the let *)
let rec add_dup (vs : var list) (vss : var list list) (ts : value_type list) (e : expr) : expr =
  match vs, vss, ts with
    | [], [], [] -> e
    | v1::vq, [v2]::vsq, t::tq ->
        ELet([], [], [v2], [t], EVar v1, add_dup vq vsq tq e)
    | v1::vs1, (v2::vs2)::vsq, t::_ ->
        let v' = one_fresh_var [t] in
        let e' = add_dup (v'::vs1) (vs2::vsq) ts e in
        ELet ([], [], [v'; v2], [t; t], Dup (v1), e')
    | v::vq, []::vsq, _::tq ->
        let e' = add_dup vq vsq tq e in
        ELet ([], [], [], [], Drop (EVar v), e')
    | _ -> failwith"weird"

(* Linearizes an expression *)
let rec linearize (env : (var list) Environnement.t) (envf : funvar Environnement.t) (env_t : environnementTypes) (e : expr) : (var list) Environnement.t * expr =
  match e with
    | ENonLinLiteral _ ->
        let v, v' = two_fresh_var [Real; Real] in
        let e' = ELet ([v], [Real], [], [], e, EMultiValue ([v], [v'])) in
        env, ELet ([], [], [v'], [Real], ELinZero Real , e')
    | EVar v ->
        (try
          let env, v' = linear_var env v in
          env, EMultiValue ([v], [v'])
        with
          Not_found -> failwith("variable " ^ v ^ " is linear"))
    | ENonLinBinOp (v1, OpTimes, v2) ->
        let v, v' = two_fresh_var [Real; Real] in
        let e' = ELet ([v], [Real], [], [], e, EMultiValue ([v], [v'])) in
        derivation_mul env e' v1 v2 v'
    | ENonLinBinOp (v1, OpPlus, v2) ->
        let v, v' = two_fresh_var [Real; Real] in
        let e' = ELet ([v], [Real], [], [], e, EMultiValue ([v], [v'])) in
        derivation_add env e' v1 v2 v'
    | ENonLinBinOp (v1, OpMinus, v2) ->
        let v, v' = two_fresh_var [Real; Real] in
        let e' = ELet ([v], [Real], [], [], e, EMultiValue ([v], [v'])) in
        derivation_min env e' v1 v2 v'
    | ENonLinBinOp (v1, OpDiv, v2) ->
        let v, v' = two_fresh_var [Real; Real] in
        let e' = ELet ([v], [Real], [], [], e, EMultiValue ([v], [v'])) in
        derivation_div env e' v1 v2 v'
    | ENonLinUnOp (OpSin, v1) ->
        let v, v' = two_fresh_var [Real; Real] in
        let e' = ELet ([v], [Real], [], [], e, EMultiValue ([v], [v'])) in
        derivation_sin env e' v1 v'
    | ENonLinUnOp (OpCos, v1) ->
        let v, v' = two_fresh_var [Real; Real] in
        let e' = ELet ([v], [Real], [], [], e, EMultiValue ([v], [v'])) in
        derivation_cos env e' v1 v'
    | ENonLinUnOp (OpExp, v1) ->
        let v, v' = two_fresh_var [Real; Real] in
        let e' = ELet ([v], [Real], [], [], e, EMultiValue ([v], [v'])) in
        derivation_exp env e' v1 v'
    | ETuple vs ->
        let vs' = find_list env vs in
        let ts = try type_list env_t vs with Not_found -> failwith"p" in
        let v1, v2 = two_fresh_var [Tuple ts; Tuple ts] in
        let e' = ELet ([v1], [Tuple ts], [], [], e, EMultiValue ([v1], [v2])) in
        env, ELet ([], [], [v2], [Tuple ts], ETuple vs', e')
    | EMultiValue (vs, []) ->
        let vs' = find_list env vs in
        env, EMultiValue (vs, vs')
    | ELet (vs, ts, [], [], e1, e2) ->
        let env_t = add_variable_types env_t vs [] ts [] in
        let vss = fresh_var_list e2 vs ts in
        let env, e1' = linearize env envf env_t e1 in
        let env = add_variable_list env vs vss in
        let env, e2' = linearize env envf env_t e2 in
        let vs' = fresh_var ts in
        let e' = add_dup vs' vss ts e2' in
        env, ELet (vs, ts, vs', ts, e1', e')
    | ENonLinUnpack (vs, ts, v, e) ->
        let vss = fresh_var_list e vs ts in
        let env_t = add_variable_types env_t vs [] ts [] in
        let env = add_variable_list env vs vss in
        let env, e' = linearize env envf env_t e in
        let env, v' = try linear_var env v with Not_found -> failwith"n" in
        let vs' = fresh_var ts in
        let e' = add_dup vs' vss ts e' in
        env, ENonLinUnpack (vs, ts, v, ELinUnpack (vs', ts, v', e'))      
    | EFunCall (f, vs, []) ->
        let f' = try Environnement.find f envf with Not_found -> failwith"o" in
        let vs' = find_list env vs in
        env, EFunCall (f', vs, vs')
    | Drop e ->
        let env, e' = linearize env envf env_t e in
        env, Drop e'
    | _ -> failwith"Linearity in a non linear program"


(* Linearizes a program *)
let rec linearize_prog (env : (var list) Environnement.t) (envf : funvar Environnement.t) (p : prog) : prog =
  match p with
    | [] -> []
    | (FunDec (f, vs, ts, [], [], e))::q ->
        let f' = fresh_fun f in
        let env_t = add_variable_types empty_env_type vs [] ts [] in
        let vss = fresh_var_list e vs ts in
        let env = add_variable_list env vs vss in
        let _, e' = linearize env envf env_t e in
        let envf = Environnement.add f f' envf in
        let p' = linearize_prog env envf q in
        let vs' = fresh_var ts in
        let e' = add_dup vs' vss ts e' in
        (FunDec (f', vs, ts, vs', ts, e'))::p'
    | _ -> failwith"Linearity in a non linear program"