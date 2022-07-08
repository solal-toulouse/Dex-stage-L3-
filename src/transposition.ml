open Syntax
open Type_checker
(* open Print *)

(* tangent : v, v', v1, v2
   cotangent : w, w', w1, w2 *)

let counter () =
  let i = ref 0 in
  let f () =
    incr i;
    !i;
  in f

let fresh_int = counter ()

(* generates a list of fresh variables for a giving list of types *)
let rec fresh_var (ts : value_type list) : var list =
  match ts with
    | [] -> []
    | _::q -> ("v'" ^ (string_of_int (fresh_int ())))::(fresh_var q)

let one_fresh_var (ts : value_type list) : var =
  match fresh_var ts with
    | [v] -> v
    | _ -> failwith"weird"

let two_fresh_var (ts : value_type list) : var * var =
  match fresh_var ts with
    | [v1; v2] -> v1, v2
    | _ -> failwith"weird"

let fresh_fun (f : funvar) : funvar =
  f ^ "'" ^ (string_of_int (fresh_int ()))
  
(* returns the list of the linear variables of *)
let add_if_linear (env : environnementTypes) (vs : var list) : var list =
  match vs with
    | [] -> []
    | v::q ->
      (match try find_type env v with Not_found -> failwith"6" with
        | MultiValueType (_, []) -> []
        | MultiValueType ([], _) -> v::q
        | _ -> failwith"weird")

(* removes the variables of the list 'vs2' from the list 'vs1' *)
let rec remove (vs1 : var list) (vs2 : var list) : var list =
  let rec aux (v : var) (vs :var list) : var list =
    match vs with
      | [] -> []
      | a::q when a = v -> aux v q
      | a::q -> a::(aux v q)
    in match vs2 with
      | [] -> vs1
      | v::q -> remove (aux v vs1) q

(* returns the list of all the free linear variables of an expression *)
let rec free_linear_variables (env : environnementTypes) (e : expr) : var list =
  match e with
    | ENonLinLiteral _ | ENonLinBinOp _ | ENonLinUnOp _ -> []
    | ENonLinUnpack (vs, ts, _, e') ->
        let env = add_variable_types env vs [] ts [] in
        free_linear_variables env e'
    | EVar v ->
        add_if_linear env [v]
    | ELinAdd (v1, v2) -> [v1; v2]
    | ELinMul (_, v2) -> [v2]
    | ETuple vs ->
        add_if_linear env vs
    | ELinZero _ -> []
    | EMultiValue (_, lvs) -> lvs
    | ELet (nlvs, nlts, lvs, lts, e1, e2) ->
        let env = add_variable_types env nlvs lvs nlts lts in
        let vs1 = free_linear_variables env e1 in
        let vs2 = free_linear_variables env e2 in
        let vs2 = remove vs2 lvs in
        vs1 @ vs2
    | ELinUnpack (vs, ts, v, e') ->
        let env = add_variable_types env [] vs [] ts in
        let vs' = free_linear_variables env e' in
        let vs' = remove vs' vs in
        v::vs'
    | EFunCall (_, _, lvs) -> lvs
    | Dup v -> [v]
    | Drop e' ->
        free_linear_variables env e'

(* returns the list of all the free non linear variables of an expression *)
let rec free_non_linear_variables (env : environnementTypes) (e : expr) : var list =
  match e with
    | ENonLinLiteral _ -> []
    | ENonLinBinOp (v1, _, v2) -> [v1; v2]
    | ENonLinUnOp (_, v) -> [v]
    | ENonLinUnpack (vs, ts, v, e') ->
        let env = add_variable_types env vs [] ts [] in
        let vs' = free_non_linear_variables env e' in
        v::(remove vs' (v::vs))
    | EVar v ->
        (try
          let _ = find_type env v in []
        with
          Not_found -> [v])
    | ELinAdd _ | ELinZero _ | Dup _-> []
    | ELinMul (v, _) -> [v]
    | ETuple [] -> []
    | ETuple (v::vs) ->
        (try
          let _ = find_type env v in []
        with
          Not_found -> v::vs)
    | EMultiValue (nlvs, _) -> nlvs
    | ELet (nlvs, nlts, lvs, lts, e1, e2) ->
        let env = add_variable_types env nlvs lvs nlts lts in
        let vs1 = free_non_linear_variables env e1 in
        let vs2 = free_non_linear_variables env e2 in
        let vs2 = remove vs2 (vs1 @ nlvs) in
        vs1 @ vs2
    | ELinUnpack (vs, ts, _, e') ->
        let env = add_variable_types env [] vs [] ts in
        free_non_linear_variables env e'
    | EFunCall (_, nlvs, _) -> nlvs
    | Drop e' ->
        free_non_linear_variables env e'

(* returns the list of the types of the variables of a list*)
let rec type_list (env : environnementTypes) (vs : var list) : value_type list =
  match vs with
    | [] -> []
    | v::q ->
        let t = (match find_type env v with
          | MultiValueType ([], [t]) -> t
          | MultiValueType ([t], []) -> t
          | _ -> failwith"weird") in
        t::(type_list env q)

(* adds a list of linear variables to the output of an expression *)
let rec add_l_output (envt : environnementTypes) (e : expr) (vs : var list) : environnementTypes * expr =
  match e with
    | EMultiValue (nlvs, lvs) -> envt, EMultiValue (nlvs, lvs @ vs)
    | ELet (nlvs, nlts, lvs, lts, e1, e2) ->
      let envt = add_variable_types envt nlvs lvs nlts lts in
      let envt, e2' = add_l_output envt e2 vs in
      envt, ELet (nlvs, nlts, lvs, lts, e1, e2')
    | ELinUnpack (lvs, lts, v, e) ->
      let envt = add_variable_types envt [] lvs [] lts in
      let envt, e' = add_l_output envt e vs in
      envt, ELinUnpack (lvs, lts, v, e')
    | ENonLinUnpack (nlvs, nlts, v, e) ->
      let envt = add_variable_types envt nlvs [] nlts [] in
      let envt, e' = add_l_output envt e vs in
      envt, ENonLinUnpack (nlvs, nlts, v, e')
    | EVar v ->
        (match try find_type envt v with Not_found -> failwith"8" with
          | MultiValueType ([], _) ->
              envt, EMultiValue ([], v::vs)
          | _ ->
              envt, EMultiValue ([v], vs))
    | ENonLinLiteral _ | ENonLinBinOp _ | ENonLinUnOp _ ->
        let v = one_fresh_var [Real] in
        let envt = add_variable_types envt [v] [] [Real] [] in
        envt, ELet ([v], [Real], [], [], e, EMultiValue([v], vs))
    | ELinAdd (v1, _) ->
        let mvt = try find_type envt v1 with Not_found -> failwith"9" in
        (match mvt with
          | MultiValueType ([], [t]) ->
              let v = one_fresh_var [t] in
              let envt = add_variable_types envt [] [v] [] [t] in
              envt, ELet ([], [], [v], [t], e, EMultiValue([], v::vs))
          | _ -> failwith"weird")
    | ELinMul _ ->
        let v = one_fresh_var [Real] in
        let envt = add_variable_types envt [] [v] [] [Real] in
        envt, ELet ([], [], [v], [Real], e, EMultiValue([], v::vs))
    | ETuple [] -> 
        let v = one_fresh_var [Tuple [Real]] in
        let envt = add_variable_types envt [v] [] [Tuple [Real]] [] in
        envt, ELet ([v], [Tuple [Real]], [], [], e, EMultiValue([v], vs))
    | ETuple (v::q) ->
      let ts' = try type_list envt (v::q) with Not_found -> failwith"1" in
      let v' = one_fresh_var ([Tuple ts']) in
      (match try find_type envt v with Not_found -> failwith"10" with
        | MultiValueType ([], _) ->
            let envt = add_variable_types envt [] [v'] [] [Tuple ts'] in
            envt, ELet ([], [], [v'], [Tuple ts'], ETuple (v::q), EMultiValue ([], v'::vs))
        | _ ->
            let envt = add_variable_types envt [v'] [] [Tuple ts'] [] in
            envt, ELet ([v'], [Tuple ts'], [], [], ETuple (v::q), EMultiValue ([v'], vs)))
    | ELinZero t -> 
        let v = one_fresh_var [t] in
        let envt = add_variable_types envt [] [v] [] [t] in
        envt, ELet ([], [], [v], [t], e, EMultiValue([], v::vs))
    | EFunCall (f, _, _) ->
        let (_, _, MultiValueType(nlts, lts)) = (try Environnement.find f envt.env_ft with Not_found -> failwith"D") in
        let nlvs2, lvs2 = fresh_var nlts, fresh_var lts in
        let envt = add_variable_types envt nlvs2 lvs2 nlts lts in
        envt, ELet (nlvs2, nlts, lvs2, lts, e, EMultiValue (nlvs2, lvs2 @ vs))
    | Dup v ->
        let mvt = try find_type envt v with Not_found -> failwith"11" in
        (match mvt with
          | MultiValueType ([], [t]) ->
              let vs' = fresh_var [t; t] in
              let envt = add_variable_types envt [] vs' [] [t; t] in
              envt, ELet ([], [], vs', [t; t], Dup v, EMultiValue ([], vs' @ vs))
          | _ -> failwith"weird")
    | Drop e' ->
        envt, ELet ([], [], [], [], Drop e', EMultiValue ([], vs))

(* adds a list of non linear variables to the output of an expression *)
let rec add_nl_output (envt : environnementTypes) (e : expr) (vs : var list) : environnementTypes * expr =
  match e with
    | EMultiValue (nlvs, lvs) -> envt, EMultiValue (nlvs @ vs, lvs)
    | ELet (nlvs, nlts, lvs, lts, e1, e2) ->
      let envt = add_variable_types envt nlvs lvs nlts lts in
      let envt, e2' = add_nl_output envt e2 vs in
      envt, ELet (nlvs, nlts, lvs, lts, e1, e2')
    | ELinUnpack (lvs, lts, v, e) ->
      let envt = add_variable_types envt [] lvs [] lts in
      let envt, e' = add_nl_output envt e vs in
      envt, ELinUnpack (lvs, lts, v, e')
    | ENonLinUnpack (nlvs, nlts, v, e) ->
      let envt = add_variable_types envt nlvs [] nlts [] in
      let envt, e' = add_nl_output envt e vs in
      envt, ENonLinUnpack (nlvs, nlts, v, e')
    | EVar v ->
        (match try find_type envt v with Not_found -> failwith"12" with
          | MultiValueType ([], _) ->
              envt, EMultiValue (vs, [v])
          | _ ->
              envt, EMultiValue (v::vs, []))
    | ENonLinLiteral _ | ENonLinBinOp _ | ENonLinUnOp _ ->
        let v = one_fresh_var [Real] in
        let envt = add_variable_types envt [v] [] [Real] [] in
        envt, ELet ([v], [Real], [], [], e, EMultiValue(v::vs, []))
    | ELinAdd (v1, _) ->
        let mvt = try find_type envt v1 with Not_found -> failwith"13" in
        (match mvt with
          | MultiValueType ([], [t]) ->
              let v = one_fresh_var [t] in
              let envt = add_variable_types envt [] [v] [] [t] in
              envt, ELet ([], [], [v], [t], e, EMultiValue(vs, [v]))
          | _ -> failwith"weird")
    | ELinMul _ ->
        let v = one_fresh_var [Real] in
        let envt = add_variable_types envt [] [v] [] [Real] in
        envt, ELet ([], [], [v], [Real], e, EMultiValue(vs, [v]))
    | ETuple [] -> 
        let v = one_fresh_var [Tuple [Real]] in
        let envt = add_variable_types envt [v] [] [Tuple [Real]] [] in
        envt, ELet ([v], [Tuple [Real]], [], [], e, EMultiValue(v::vs, []))
    | ETuple (v::q) ->
      let ts' = try type_list envt (v::q) with Not_found -> failwith"2" in
      let v' = one_fresh_var ([Tuple ts']) in
      (match try find_type envt v with Not_found -> failwith"14" with
        | MultiValueType ([], _) ->
            let envt = add_variable_types envt [] [v'] [] [Tuple ts'] in
            envt, ELet ([], [], [v'], [Tuple ts'], ETuple (v::q), EMultiValue (vs, [v']))
        | _ ->
            let envt = add_variable_types envt [v'] [] [Tuple ts'] [] in
            envt, ELet ([v'], [Tuple ts'], [], [], ETuple (v::q), EMultiValue (v'::vs, [])))
    | ELinZero t -> 
        let v = one_fresh_var [t] in
        let envt = add_variable_types envt [] [v] [] [t] in
        envt, ELet ([], [], [v], [t], e, EMultiValue(vs, [v]))
    | EFunCall (f, _, _) ->
        let (_, _, MultiValueType(nlts2, lts2)) = try Environnement.find f envt.env_ft with Not_found -> failwith"E" in
        let nlvs2, lvs2 = fresh_var nlts2, fresh_var lts2 in
        let envt = add_variable_types envt nlvs2 lvs2 nlts2 lts2 in
        envt, ELet (nlvs2, nlts2, lvs2, lts2, e, EMultiValue (nlvs2 @ vs, lvs2))
    | Dup v ->
        let mvt = try find_type envt v with Not_found -> failwith"15" in
        (match mvt with
          | MultiValueType ([], [t]) ->
              let vs' = fresh_var [t; t] in
              let envt = add_variable_types envt [] vs' [] [t; t] in
              envt, ELet ([], [], vs', [t; t], Dup v, EMultiValue (vs, vs'))
          | _ -> failwith"weird")
    | Drop e' ->
        envt, ELet ([], [], [], [], Drop e', EMultiValue (vs, []))

(* Returns a multivalue of zeros with the type 'nlts, lts' *)
let zero (nlts : value_type list) (lts : value_type list) : expr =
  let nlvs, lvs = fresh_var nlts, fresh_var lts in
  let rec auxnl nlts' nlvs' =
    match nlts', nlvs' with
      | [], [] -> EMultiValue (nlvs, lvs)
      | t::tq, v::vq ->
          ELet ([v], [t], [], [], ELinZero t, auxnl tq vq)
      | _ -> failwith"weird"
  in let rec auxl lts' lvs' =
    match lts', lvs' with
      | [], [] -> auxnl nlts nlvs
      | t::tq, v::vq ->
          ELet ([], [], [v], [t], ELinZero t, auxl tq vq)
      | _ -> failwith"weird"
  in auxl lts lvs

let aux_let (env : environnementTypes) (e : expr) (lvs : var list) : var list * value_type list * var list * value_type list * var list * value_type list =
  let ws = free_linear_variables env e in
  let ts = try type_list env ws with Not_found -> failwith"7" in
  let ws1 = remove ws lvs in
  let ws2 = remove ws ws1 in
  let ts1 = try type_list env ws1 with Not_found -> failwith"4" in
  let ts2 = try type_list env ws2 with Not_found -> failwith"5" in
  let rec aux ws ts ws1 ws2 = 
    match ws, ts, ws1, ws2 with
      | [], _, _, _ -> [], [], []
      | w::q, t::qt, w1::q1, ws2 when w = w1 ->
          let w' = one_fresh_var [t] in
          let ws', ws1', ws2' = aux q qt q1 ws2 in
          w'::ws', w'::ws1', ws2'
      | w::q, t::qt, ws1, w2::q2 when w = w2 ->
          let w' = one_fresh_var [t] in
          let ws', ws1', ws2' = aux q qt ws1 q2 in
          w'::ws', ws1', w'::ws2'
      | _ -> failwith"weird"
  in let ws, ws1, ws2 = aux ws ts ws1 ws2 in
  ws, ts, ws1, ts1, ws2, ts2

let transpose_name_function (f : funvar) = (f ^ "'")

(* Transposition *)

(* returns the transposition of an unzipped expression *)
(*'env' stores the input of 'e', and it's used when we are looking for the type of the output while 'envt' store the type of the variables of the transposition of 'e' *)
let rec transpose_expr (env : environnementTypes) (envt : environnementTypes) (v_out : var list) (t_out : value_type list) (e : expr) : environnementTypes * environnementTypes * expr =
  match e, v_out with
    | ENonLinLiteral _, [] | ENonLinBinOp _, [] | ENonLinUnOp _, [] -> envt, env, e
    | ENonLinUnpack (vs, ts, v, e1), [] ->
        let env = add_variable_types env  vs [] ts [] in
        let envt = add_variable_types envt vs [] ts [] in
        let envt, env, e2 = transpose_expr env envt v_out t_out e1 in
        envt, env, ENonLinUnpack (vs, ts, v, e2)
    | EVar _, [w] -> envt, env, EVar w
    | ELinAdd _, [w] -> envt, env, Dup w
    | ELinMul (v1, _), [w] -> envt, env, ELinMul (v1, w)
    | ETuple [], _ -> envt, env, ETuple []
    | ETuple (v::q), _ ->
        (match try find_type env v with Not_found -> failwith"16" with
          | MultiValueType([], [_]) ->
              let ts = try type_list env (v::q) with Not_found -> failwith"3" in
              let ws = fresh_var ts in
              let envt = add_variable_types envt [] ws [] ts in
              let w = List.hd v_out in
              envt, env, ELinUnpack (ws, ts, w, EMultiValue ([], ws))
          | MultiValueType([_], []) -> envt, env, e
          | _ -> failwith "weird")
    | ELinZero _, [w] -> envt, env, Drop (EVar w)
    | EMultiValue (vs, _), lws -> envt, env, EMultiValue(vs, lws)
    | ELet ([], [], lvs, lts, e1, e2), _ ->
        let env = add_variable_types env [] lvs [] lts in
        let ws, ts, ws1, ts1, ws2, ts2 = aux_let env e2 lvs in
        let envt' = add_variable_types envt [] (ws1 @ ws2) [] (ts1 @ ts2) in
        let envt, env, e1' = transpose_expr env envt' ws2 ts2 e1 in
        let envt, env, e2' = transpose_expr env envt v_out t_out e2 in
        let _, e1' = add_l_output envt' e1' ws1 in
        envt, env, ELet ([], [], ws, ts, e2', e1')
    | ELet (nlvs, nlts, [], [], e1, e2), _ ->
        let env = add_variable_types env nlvs [] nlts [] in
        let envt = add_variable_types envt nlvs [] nlts [] in
        let envt, env, e1' = transpose_expr env envt [] [] e1 in
        let envt, env, e2' = transpose_expr env envt v_out t_out e2 in
        envt, env, ELet (nlvs, nlts, [], [], e1', e2')
    | ELinUnpack (vs, ts, _, EMultiValue([], vs')), ws when vs = vs' ->
        let env = add_variable_types env [] vs [] ts in
        envt, env, ETuple ws
    | ELinUnpack (vs, ts, v, e'), _ -> (* we come back to the previous case *)
        let vs' = fresh_var ts in
        let envt = add_variable_types envt [] vs' [] ts in
        let e1 = ELinUnpack(vs', ts, v, EMultiValue([], vs')) in
        let e2 = ELet ([], [], vs, ts, e1, e') in
        transpose_expr env envt v_out t_out e2
    | EFunCall (f, nlvs, _), ws ->
        envt, env, EFunCall (transpose_name_function f, nlvs, ws)
    | Dup _, [w1; w2] -> envt, env, ELinAdd (w1, w2)
    | Drop (EMultiValue (nlvs, lvs)), [] ->
        let _, MultiValueType (nlts, lts) = read_types env nlvs lvs in
        envt, env, zero nlts lts
    | Drop e', [] ->
        let _, MultiValueType (nlts, lts) = type_checker env e' in
        let nlvs, lvs = fresh_var nlts, fresh_var lts in
        transpose_expr env envt [] [] (ELet (nlvs, nlts, lvs, lts, e', Drop (EMultiValue (nlvs, lvs))))
    | _ -> failwith"untransposable expression"

(* transpose a program *)
let rec transpose_prog (env : environnementTypes) (envt : environnementTypes) (p : prog) : prog =
  match p with
    | [] -> []
    | (FunDec (f, nlvs, nlts, lvs, lts, e))::q ->
      let env = add_variable_types env nlvs lvs nlts lts in
      let _, MultiValueType (nlts', lts') = type_checker env e in
      let f' = transpose_name_function f in
      let env_ft = Environnement.add f (nlts, lts, MultiValueType (nlts', lts')) env.env_ft in
      let envt_ft = Environnement.add f' (nlts, lts', MultiValueType (nlts', lts)) envt.env_ft in
      let env = { env_nlt = env.env_nlt; env_lt = env.env_lt; env_ft = env_ft } in
      let envt = { env_nlt = envt.env_nlt; env_lt = envt.env_lt; env_ft = envt_ft } in
      let lvs2 = fresh_var lts' in
      let _, _, e' = transpose_expr env envt lvs2 lts' e in
      (FunDec (f', nlvs, nlts, lvs2, lts', e'))::(transpose_prog env envt q)