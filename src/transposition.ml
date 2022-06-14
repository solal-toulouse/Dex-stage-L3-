open Syntax
open Type_checker
open Print

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

(* returns the list of the linear variables of *)
let add_if_linear (env : environnementTypes) (vs : var list) : var list =
  match vs with
    | [] -> []
    | v::q ->
      (match find_type env v with
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
    | EDec (nlvs, nlts, lvs, lts, e1, e2) ->
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
        v::(remove vs' vs)
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
    | EDec (nlvs, nlts, lvs, lts, e1, e2) ->
        let env = add_variable_types env nlvs lvs nlts lts in
        let vs1 = free_non_linear_variables env e1 in
        let vs2 = free_non_linear_variables env e2 in
        let vs2 = remove vs2 nlvs in
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
    | EDec (nlvs, nlts, lvs, lts, e1, e2) ->
      let envt = add_variable_types envt nlvs lvs nlts lts in
      let envt, e2' = add_l_output envt e2 vs in
      envt, EDec (nlvs, nlts, lvs, lts, e1, e2')
    | ELinUnpack (lvs, lts, v, e) ->
      let envt = add_variable_types envt [] lvs [] lts in
      let envt, e' = add_l_output envt e vs in
      envt, ELinUnpack (lvs, lts, v, e')
    | ENonLinUnpack (nlvs, nlts, v, e) ->
      let envt = add_variable_types envt nlvs [] nlts [] in
      let envt, e' = add_l_output envt e vs in
      envt, ENonLinUnpack (nlvs, nlts, v, e')
    | EVar v ->
        (match find_type envt v with
          | MultiValueType ([], _) ->
              envt, EMultiValue ([], v::vs)
          | _ ->
              envt, EMultiValue ([v], vs))
    | ENonLinLiteral _ | ENonLinBinOp _ | ENonLinUnOp _ ->
        let vs' = fresh_var [Real] in
        let envt = add_variable_types envt vs' [] [Real] [] in
        (match vs' with
          | [v] ->
              envt, EDec ([v], [Real], [], [], e, EMultiValue([v], vs))
          | _ -> failwith"weird")
    | ELinAdd (v1, _) ->
        let mvt = find_type envt v1 in
        (match mvt with
          | MultiValueType ([], [t]) ->
              let vs' = fresh_var [t] in
              let envt = add_variable_types envt [] vs' [] [t] in
              (match vs' with
                | [v] ->
                    envt, EDec ([], [], [v], [t], e, EMultiValue([], v::vs))
                | _ -> failwith"weird")
          | _ -> failwith"weird")
    | ELinMul _ ->
        let vs' = fresh_var [Real] in
        let envt = add_variable_types envt [] vs' [] [Real] in
        (match vs' with
          | [v] ->
              envt, EDec ([], [], [v], [Real], e, EMultiValue([], v::vs))
          | _ -> failwith"weird")
    | ETuple [] -> 
        let vs' = fresh_var [Tuple [Real]] in
        let envt = add_variable_types envt vs' [] [Tuple [Real]] [] in
        (match vs' with
          | [v] ->
              envt, EDec ([v], [Tuple [Real]], [], [], e, EMultiValue([v], vs))
          | _ -> failwith"weird")
    | ETuple (v::q) ->
      let ts' = type_list envt (v::q) in
      let vs' = fresh_var ([Tuple ts']) in
      (match find_type envt v with
        | MultiValueType ([], _) ->
            (match vs' with
              | [v'] ->
                  let envt = add_variable_types envt [] vs' [] [Tuple ts'] in
                  envt, EDec ([], [], [v'], [Tuple ts'], ETuple (v::q), EMultiValue ([], v'::vs))
              | _ -> failwith"weird")
        | _ ->
            (match vs' with
              | [v'] ->
                  let envt = add_variable_types envt vs' [] [Tuple ts'] [] in
                  envt, EDec ([v'], [Tuple ts'], [], [], ETuple (v::q), EMultiValue ([v'], vs))
              | _ -> failwith"weird"))
    | ELinZero t -> 
        let vs' = fresh_var [t] in
        let envt = add_variable_types envt [] vs' [] [t] in
        (match vs' with
          | [v] ->
              envt, EDec ([], [], [v], [t], e, EMultiValue([], v::vs))
          | _ -> failwith"weird")
    | EFunCall (f, _, _) ->
        let (_, _, MultiValueType(nlts, lts)) = Environnement.find f envt.env_ft in
        let nlvs2, lvs2 = fresh_var nlts, fresh_var lts in
        let envt = add_variable_types envt nlvs2 lvs2 nlts lts in
        envt, EDec (nlvs2, nlts, lvs2, lts, e, EMultiValue (nlvs2, lvs2 @ vs))
    | Dup v ->
        let mvt = find_type envt v in
        (match mvt with
          | MultiValueType ([], [t]) ->
              let vs' = fresh_var [t; t] in
              let envt = add_variable_types envt [] vs' [] [t; t] in
              envt, EDec ([], [], vs', [t; t], Dup v, EMultiValue ([], vs' @ vs))
          | _ -> failwith"weird")
    | Drop e' ->
        envt, EDec ([], [], [], [], Drop e', EMultiValue ([], vs))

(* adds a list of non linear variables to the output of an expression *)
let rec add_nl_output (envt : environnementTypes) (e : expr) (vs : var list) : environnementTypes * expr =
  match e with
    | EMultiValue (nlvs, lvs) -> envt, EMultiValue (nlvs @ vs, lvs)
    | EDec (nlvs, nlts, lvs, lts, e1, e2) ->
      let envt = add_variable_types envt nlvs lvs nlts lts in
      let envt, e2' = add_nl_output envt e2 vs in
      envt, EDec (nlvs, nlts, lvs, lts, e1, e2')
    | ELinUnpack (lvs, lts, v, e) ->
      let envt = add_variable_types envt [] lvs [] lts in
      let envt, e' = add_nl_output envt e vs in
      envt, ELinUnpack (lvs, lts, v, e')
    | ENonLinUnpack (nlvs, nlts, v, e) ->
      let envt = add_variable_types envt nlvs [] nlts [] in
      let envt, e' = add_nl_output envt e vs in
      envt, ENonLinUnpack (nlvs, nlts, v, e')
    | EVar v ->
        (match find_type envt v with
          | MultiValueType ([], _) ->
              envt, EMultiValue (vs, [v])
          | _ ->
              envt, EMultiValue (v::vs, []))
    | ENonLinLiteral _ | ENonLinBinOp _ | ENonLinUnOp _ ->
        let vs' = fresh_var [Real] in
        let envt = add_variable_types envt vs [] [Real] [] in
        (match vs' with
          | [v] ->
              envt, EDec ([v], [Real], [], [], e, EMultiValue(v::vs, []))
          | _ -> failwith"weird")
    | ELinAdd (v1, _) ->
        let mvt = find_type envt v1 in
        (match mvt with
          | MultiValueType ([], [t]) ->
              let vs' = fresh_var [t] in
              let envt = add_variable_types envt [] vs' [] [t] in
              (match vs' with
                | [v] ->
                    envt, EDec ([], [], [v], [t], e, EMultiValue(vs, [v]))
                | _ -> failwith"weird")
          | _ -> failwith"weird")
    | ELinMul _ ->
        let vs' = fresh_var [Real] in
        let envt = add_variable_types envt [] vs' [] [Real] in
        (match vs' with
          | [v] ->
              envt, EDec ([], [], [v], [Real], e, EMultiValue(vs, [v]))
          | _ -> failwith"weird")
    | ETuple [] -> 
        let vs' = fresh_var [Tuple [Real]] in
        let envt = add_variable_types envt vs' [] [Tuple [Real]] [] in
        (match vs' with
          | [v] ->
              envt, EDec ([v], [Tuple [Real]], [], [], e, EMultiValue(v::vs, []))
          | _ -> failwith"weird")
    | ETuple (v::q) ->
      let ts' = type_list envt (v::q) in
      let vs' = fresh_var ([Tuple ts']) in
      (match find_type envt v with
        | MultiValueType ([], _) ->
            (match vs' with
              | [v'] ->
                  let envt = add_variable_types envt [] vs' [] [Tuple ts'] in
                  envt, EDec ([], [], [v'], [Tuple ts'], ETuple (v::q), EMultiValue (vs, [v']))
              | _ -> failwith"weird")
        | _ ->
            (match vs' with
              | [v'] ->
                  let envt = add_variable_types envt vs' [] [Tuple ts'] [] in
                  envt, EDec ([v'], [Tuple ts'], [], [], ETuple (v::q), EMultiValue (v'::vs, []))
              | _ -> failwith"weird"))
    | ELinZero t -> 
        let vs' = fresh_var [t] in
        let envt = add_variable_types envt [] vs' [] [t] in
        (match vs' with
          | [v] ->
              envt, EDec ([], [], [v], [t], e, EMultiValue(vs, [v]))
          | _ -> failwith"weird")
    | EFunCall (f, _, _) ->
        let (_, _, MultiValueType(nlts2, lts2)) = Environnement.find f envt.env_ft in
        let nlvs2, lvs2 = fresh_var nlts2, fresh_var lts2 in
        let envt = add_variable_types envt nlvs2 lvs2 nlts2 lts2 in
        envt, EDec (nlvs2, nlts2, lvs2, lts2, e, EMultiValue (nlvs2 @ vs, lvs2))
    | Dup v ->
        let mvt = find_type envt v in
        (match mvt with
          | MultiValueType ([], [t]) ->
              let vs' = fresh_var [t; t] in
              let envt = add_variable_types envt [] vs' [] [t; t] in
              envt, EDec ([], [], vs', [t; t], Dup v, EMultiValue (vs, vs'))
          | _ -> failwith"weird")
    | Drop e' ->
        envt, EDec ([], [], [], [], Drop e', EMultiValue (vs, []))

(* Deletes 'let (;) = (;) in ...' *)
let rec simplify (e : expr) : expr =
  match e with
    | ENonLinLiteral _ | ENonLinBinOp _ | ENonLinUnOp _ | EVar _ | ELinAdd _ | ELinZero _ | Dup _ | ELinMul _ | ETuple _ | EMultiValue _ | EFunCall _-> e
    | EDec ([], [], [], [], EMultiValue ([], []), e') -> simplify e'
    | EDec ([], [], [], [], Drop e', EMultiValue ([], [])) -> Drop (simplify e')
    | ENonLinUnpack ([], [], _, e') -> simplify e'
    | ELinUnpack ([], [], _, e') -> simplify e'
    | ENonLinUnpack (vs, ts, v, e') ->
        ENonLinUnpack (vs, ts, v, simplify e')
    | EDec (nlvs, nlts, lvs, lts, e1, e2) -> 
        EDec (nlvs, nlts, lvs, lts, simplify e1, simplify e2)
    | ELinUnpack (vs, ts, v, e') ->
        ELinUnpack (vs, ts, v, simplify e')
    | Drop e' ->
        Drop (simplify e')

let zero (nlts : value_type list) (lts : value_type list) : expr =
  let rec auxnl nlvs lvs nlts =
    match nlts with
      | [] -> EMultiValue (nlvs, lvs)
      | t::q ->
          let vs' = fresh_var [t] in
          (match vs' with
            | [v] -> EDec ([v], [t], [], [], ELinZero t, auxnl (v::nlvs) lvs q)
            | _ -> failwith"weird")
  in let rec auxl nlvs lvs lts =
    match lts with
      | [] -> auxnl nlvs lvs nlts
      | t::q ->
          let vs' = fresh_var [t] in
          (match vs' with
            | [v] -> EDec ([], [], [v], [t], ELinZero t, auxl nlvs (v::lvs) q)
            | _ -> failwith"weird")
  in auxl [] [] lts

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
    | ETuple (v::q), [w] ->
        (match find_type env v with
          | MultiValueType([], [_]) ->
              let ts = type_list env (v::q) in
              let ws = fresh_var ts in
              let envt = add_variable_types envt [] ws [] ts in
              envt, env, ELinUnpack (ws, ts, w, EMultiValue ([], ws))
          | MultiValueType([_], []) -> envt, env, e
          | _ -> failwith "weird")
    | ELinZero _, [w] -> envt, env, Drop (EVar w)
    | EMultiValue (vs, _), lws -> envt, env, EMultiValue(vs, lws)
    | EDec ([], [], lvs, lts, e1, e2), _ ->
        let env = add_variable_types env [] lvs [] lts in
        let ws = free_linear_variables env e2 in
        let ws1 = remove ws lvs in
        let ws2 = remove ws ws1 in
        let ts1 = type_list env ws1 in
        let ws1 = fresh_var ts1 in
        let ts2 = type_list env ws2 in
        let ws2 = fresh_var ts2 in
        let envt = add_variable_types envt [] (ws1 @ ws2) [] (ts1 @ ts2) in
        let envt, env, e1' = transpose_expr env envt ws2 ts2 e1 in
        let envt, env, e2' = transpose_expr env envt v_out t_out e2 in
        let envt, e1' = add_l_output envt e1' ws1 in
        envt, env, EDec ([], [], ws1 @ ws2, ts1 @ ts2, e2', e1')
    | EDec (nlvs, nlts, [], [], e1, e2), _ ->
        let env = add_variable_types env nlvs [] nlts [] in
        let envt = add_variable_types envt nlvs [] nlts [] in
        let envt, env, e' = transpose_expr env envt v_out t_out e2 in
        envt, env, EDec (nlvs, nlts, [], [], e1, e')
    | ELinUnpack (vs, ts, _, EMultiValue([], vs')), ws when vs = vs' ->
        let env = add_variable_types env [] vs [] ts in
        envt, env, ETuple ws
    | ELinUnpack (vs, ts, v, e'), _ -> (* we come back to the previous case *)
        let vs2 = fresh_var ts in
        let envt = add_variable_types envt [] vs2 [] ts in
        let e1 = ELinUnpack(vs2, ts, v, EMultiValue([], vs2)) in
        let e2 = EDec ([], [], vs, ts, e1, e') in
        transpose_expr env envt v_out t_out e2
    | EFunCall (f, nlvs, _), ws ->
        envt, env, EFunCall (f ^ "'", nlvs, ws)
    | Dup _, [w1; w2] -> envt, env, ELinAdd (w1, w2)
    | Drop (EMultiValue (nlvs, lvs)), [] ->
        let _, MultiValueType (nlts, lts) = read_types env nlvs lvs in
        envt, env, zero nlts lts
    | Drop e', [] ->
        let _, MultiValueType (nlts, lts) = type_checker env e' in
        let nlvs, lvs = fresh_var nlts, fresh_var lts in
        transpose_expr env envt [] [] (EDec (nlvs, nlts, lvs, lts, e', Drop (EMultiValue (nlvs, lvs))))
    | _ ->
        print_expr e;
        Printf.fprintf stderr "\n";
        print_var_list v_out;
        Printf.fprintf stderr "\n";
        failwith"error"

(* transpose a program *)
let rec transpose_prog (env : environnementTypes) (envt : environnementTypes) (p : prog) : prog =
  match p with
    | [] -> []
    | (FunDec (f, nlvs, nlts, lvs, lts, e))::q ->
      let env = add_variable_types env nlvs lvs nlts lts in
      let _, MultiValueType (nlts', lts') = type_checker env e in
      let f' = if (f = "main") then "main" else f ^ "'" in
      let env_ft = Environnement.add f (nlts, lts, MultiValueType (nlts', lts')) env.env_ft in
      let envt_ft = Environnement.add f' (nlts', lts', MultiValueType (nlts, lts)) envt.env_ft in
      let env = { env_nlt = env.env_nlt; env_lt = env.env_lt; env_ft = env_ft } in
      let envt = { env_nlt = envt.env_nlt; env_lt = envt.env_lt; env_ft = envt_ft } in
      let lvs2 = fresh_var lts' in
      let _, _, e' = transpose_expr env envt lvs2 lts' e in
      (FunDec (f', nlvs, nlts, lvs2, lts', simplify e'))::(transpose_prog env envt q)