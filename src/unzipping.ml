open Syntax
open Transposition
(* open Print *)
open Type_checker

type context =
  | CEmpty
  | CDec of var list * value_type list * var list * value_type list * expr * context
  | CLinUnpack of var list * value_type list * var * context
  | CNonLinUnpack of var list * value_type list * var * context

let empty_expr = EMultiValue ([], [])

let context_of_expr (e : expr) : context =
    match e with
        | EDec (nlvs, nlts, lvs, lts, e1, _) ->
            CDec (nlvs, nlts, lvs, lts, e1, CEmpty)
        | ENonLinUnpack (vs, ts, v, _) ->
            CNonLinUnpack (vs, ts, v, CEmpty)
        | ELinUnpack (vs, ts, v, _) ->
            CLinUnpack (vs, ts, v, CEmpty)
        | _ -> failwith"wrong form for a context"

let rec compose_context (c1 : context) (c2 : context) : context =
  match c1 with
    | CEmpty -> c2
    | CDec (nlvs, lvs, nlts, lts, e1, CEmpty) ->
        CDec (nlvs, lvs, nlts, lts, e1, c2)
    | CNonLinUnpack (vs, ts, v, CEmpty) ->
        CNonLinUnpack (vs, ts, v, c2)
    | CLinUnpack (vs, ts, v, CEmpty) ->
        CLinUnpack (vs, ts, v, c2)
    | CDec (nlvs, lvs, nlts, lts, e1, c) ->
        CDec (nlvs, lvs, nlts, lts, e1, compose_context c c2)
    | CNonLinUnpack (vs, ts, v, c) ->
        CNonLinUnpack (vs, ts, v, compose_context c c2)
    | CLinUnpack (vs, ts, v, c) ->
        CLinUnpack (vs, ts, v, compose_context c c2)

let rec fill_context (c : context) (e : expr) : expr =
    match c with
        | CEmpty -> e
        | CDec (nlvs, nlts, lvs, lts, e1, CEmpty) ->
            EDec (nlvs, nlts, lvs, lts, e1, e)
        | CNonLinUnpack (vs, ts, v, CEmpty) ->
            ENonLinUnpack (vs, ts, v, e)
        | CLinUnpack (vs, ts, v, CEmpty) ->
            ELinUnpack (vs, ts, v, e)
        | CDec (nlvs, nlts, lvs, lts, e1, c') ->
            EDec (nlvs, nlts, lvs, lts, e1, fill_context c' e)
        | CNonLinUnpack (vs, ts, v, c') ->
            ENonLinUnpack (vs, ts, v, fill_context c' e)
        | CLinUnpack (vs, ts, v, c') ->
            ELinUnpack (vs, ts, v, fill_context c' e)

let find_unzip (env : environnementUnzipping) (v : var) : multivalue_type =
  try
    let t = Environnement.find v env.env_nlu in
    MultiValueType ([t], [])
  with
    Not_found -> 
      try
        let t = Environnement.find v env.env_lu in
        MultiValueType ([], [t])
      with
        Not_found -> failwith ("variable not found : " ^ v)

let rec type_list_unzip (env : environnementUnzipping) (vs : var list) : value_type list =
  match vs with
    | [] -> []
    | v::q ->
        (Environnement.find v env.env_lu)::(type_list_unzip env q)

let add_variable_unzip (env : environnementUnzipping) (nlvs : var list) (lvs : var list) (nlts : value_type list) (lts : value_type list) : environnementUnzipping =
  let env_nlu, env_lu, env_fu = env.env_nlu, env.env_lu, env.env_fu in
  let rec aux vs ts env_t =
    match vs, ts with
      | [], [] -> env_t
      | [], _| _, [] -> failwith"type error"
      | a::b, c::d ->
        let env_t = Environnement.add a c env_t in
        aux b d env_t
  in { env_nlu = aux nlvs nlts env_nlu; env_lu = aux lvs lts env_lu; env_fu = env_fu }
        
let rec add_output_unzip (env : environnementUnzipping) (e : expr) (vs : var list) : expr =
  match e with
    | EMultiValue (nlvs, lvs) -> EMultiValue (nlvs, lvs @ vs)
    | EDec (nlvs, nlts, lvs, lts, e1, e2) ->
      let env = add_variable_unzip env nlvs lvs nlts lts in
      EDec (nlvs, nlts, lvs, lts, e1, add_output_unzip env e2 vs)
    | ELinUnpack (lvs, lts, v, e) ->
      let env = add_variable_unzip env [] lvs [] lts in
      ELinUnpack (lvs, lts, v, add_output_unzip env e vs)
    | ENonLinUnpack (nlvs, nlts, v, e) ->
      let env = add_variable_unzip env nlvs [] nlts [] in
      ENonLinUnpack (nlvs, nlts, v, add_output_unzip env e vs)
    | EVar v ->
        (match find_unzip env v with
          | MultiValueType ([], _) ->
              EMultiValue ([], v::vs)
          | _ ->
              EMultiValue ([v], vs))
    | ENonLinLiteral _ | ENonLinBinOp _ | ENonLinUnOp _ ->
        let vs' = fresh_var [Real] in
        (match vs' with
          | [v] ->
              EDec ([v], [Real], [], [], e, EMultiValue([v], vs))
          | _ -> failwith"weird")
    | ELinAdd (v1, _) ->
        let mvt = find_unzip env v1 in
        (match mvt with
          | MultiValueType ([], [t]) ->
              let vs' = fresh_var [t] in
              (match vs' with
                | [v] ->
                    EDec ([], [], [v], [t], e, EMultiValue([], v::vs))
                | _ -> failwith"weird")
          | _ -> failwith"weird")
    | ELinMul _ ->
        let vs' = fresh_var [Real] in
        (match vs' with
          | [v] ->
              EDec ([], [], [v], [Real], e, EMultiValue([], v::vs))
          | _ -> failwith"weird")
    | ETuple [] -> 
        let vs' = fresh_var [Tuple [Real]] in
        (match vs' with
          | [v] ->
              EDec ([v], [Tuple [Real]], [], [], e, EMultiValue([v], vs))
          | _ -> failwith"weird")
    | ETuple (v::q) ->
      let ts' = type_list_unzip env (v::q) in
      let vs' = fresh_var ([Tuple ts']) in
      (match find_unzip env v with
        | MultiValueType ([], _) ->
            (match vs' with
              | [v'] -> EDec ([], [], [v'], [Tuple ts'], ETuple (v::q), EMultiValue ([], v'::vs))
              | _ -> failwith"weird")
        | _ ->
            (match vs' with
              | [v'] -> EDec ([v'], [Tuple ts'], [], [], ETuple (v::q), EMultiValue ([v'], vs))
              | _ -> failwith"weird"))
    | ELinZero t -> 
        let vs' = fresh_var [t] in
        (match vs' with
          | [v] ->
              EDec ([], [], [v], [t], e, EMultiValue([], v::vs))
          | _ -> failwith"weird")
    | EFunCall (_, nlvs, lvs) ->
        let nlts, lts = type_list_unzip env nlvs, type_list_unzip env lvs in
        let nlvs2, lvs2 = fresh_var nlts, fresh_var lts in
        EDec (nlvs2, nlts, lvs2, lts, e, EMultiValue (nlvs2, lvs2 @ vs))
    | Dup v ->
        let mvt = find_unzip env v in
        (match mvt with
          | MultiValueType ([], [t]) ->
              let vs' = fresh_var [t; t] in
              EDec ([], [], vs', [t; t], Dup v, EMultiValue ([], vs' @ vs))
          | _ -> failwith"weird")
    | Drop _ -> EMultiValue ([], vs)

let add_if_non_linear (env : environnementUnzipping) (vs : var list) : var list =
  match vs with
    | [] -> []
    | v::q ->
      (match find_unzip env v with
        | MultiValueType (_, []) -> v::q
        | MultiValueType ([], _) -> []
        | _ -> failwith"weird")

let rec unzip (env : environnementUnzipping) (e : expr) : context * expr * expr =
  match e with
    | ENonLinLiteral _ | ENonLinBinOp _ | ENonLinUnOp _ ->
        CEmpty, e, empty_expr 
    | EVar v ->
        (match find_unzip env v with
          | MultiValueType ([], _) ->
              CEmpty, empty_expr , EVar v
          | _ -> CEmpty, EVar v, empty_expr )
    | ELinAdd _ | ELinMul _ | ELinZero _ | Dup _ ->
        CEmpty, empty_expr , e
    | ETuple [] ->
        CEmpty, ETuple [], empty_expr 
    | ETuple (x::_) ->
        (match find_unzip env x with
          | MultiValueType ([], _) ->
              CEmpty, empty_expr, e
          | _ -> CEmpty, e, empty_expr)
    | EMultiValue (nlvs, lvs) ->
        CEmpty, EMultiValue (nlvs, []), EMultiValue ([], lvs)
    | EDec (nlvs, nlts, lvs, lts, e1, e2) ->
        let env = add_variable_unzip env nlvs lvs nlts lts in
        let c1, nle1, le1 = unzip env e1 in
        let c2, nle2, le2 = unzip env e2 in
        let c = CDec (nlvs, nlts, [], [], nle1, CEmpty) in
        let c = compose_context c1 (compose_context c c2) in
        c, nle2, EDec ([], [], lvs, lts, le1, le2)
    | ENonLinUnpack (vs, ts, v, e1) ->
        let env = add_variable_unzip env vs [] ts [] in
        let c, nle, le = unzip env e1 in
        let c' = CNonLinUnpack (vs, ts, v, CEmpty) in
        let c' = compose_context c' c in
        c', nle, le
    | ELinUnpack (vs, ts, v, e1) ->
        let env = add_variable_unzip env [] vs [] ts in
        let c, nle, le = unzip env e1 in
        c, nle, ELinUnpack (vs, ts, v, le)
    | EFunCall (f, nlvs, lvs) ->
        let (nlf, nlts, lf, lts) = Environnement.find f env.env_fu in
        let nlvs2, lvs2 = fresh_var nlts, fresh_var lts in
        let c = CDec (nlvs2, nlts, lvs2, lts, EFunCall (nlf, nlvs, []), CEmpty) in
        c, EMultiValue (nlvs2, []), EFunCall (lf, lvs, [])
    | Drop e' ->
        let env, e1, e2 = unzip env e' in
        env, Drop e1, Drop e2

let unzip_prog (p : prog) : prog * prog =
    let rec aux (env_fu : environnementFunctionUnzipping) (env_ft : environnementFunctionTypes) (p : prog) : prog * prog =
      match p with
        | [] -> [], []
        | (FunDec (f, nlvs, nlts, lvs, lts, e))::q ->
          let fnonlin, flin = f ^ "'nonlin", f ^ "'lin" in
          let envt = add_variable_types { env_nlt = Environnement.empty; env_lt = Environnement.empty; env_ft = env_ft } nlvs lvs nlts lts in
          let envt, mvt = type_checker envt e in
          let MultiValueType (nlts2, lts2) = mvt in
          let env_fu = Environnement.add f (fnonlin, nlts2, flin, lts2) env_fu in
          let env_ft = Environnement.add f (nlts, lts, mvt) env_ft in
          let envu = { env_nlu = Environnement.empty; env_lu = Environnement.empty; env_fu = env_fu } in
          let envu = add_variable_unzip envu nlvs lvs nlts lts in
          let c, nle, le = unzip envu e in
          let p1, p2 = aux env_fu env_ft q in
          let vs = free_non_linear_variables envt le in
          let ts = type_list envt vs in
          let _, nle2 = add_nl_output envt (fill_context c nle) vs in
          let nle2, le = simplify nle2, simplify le in
          (FunDec (f ^ "'nonlin", nlvs, nlts, [], [], nle2))::p1, (FunDec (f ^"'lin", vs, ts, lvs, lts, le))::p2
    in aux Environnement.empty Environnement.empty p