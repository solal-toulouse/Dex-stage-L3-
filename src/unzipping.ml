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

(* Transforms an expression in a context *)
let context_of_expr (e : expr) : context =
    match e with
        | EDec (nlvs, nlts, lvs, lts, e1, _) ->
            CDec (nlvs, nlts, lvs, lts, e1, CEmpty)
        | ENonLinUnpack (vs, ts, v, _) ->
            CNonLinUnpack (vs, ts, v, CEmpty)
        | ELinUnpack (vs, ts, v, _) ->
            CLinUnpack (vs, ts, v, CEmpty)
        | _ -> failwith"wrong form for a context"

(* Fills the hole of 'c1' with 'c2' to obtain a new context *)
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

(* Fills the hole of 'c' with 'e' to obtain an expression *)
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
      
(* Unzip an expression *)
let rec unzip (env_fu : environnementFunctionUnzipping) (envt : environnementTypes) (e : expr) :environnementTypes * context * expr * expr =
  match e with
    | ENonLinLiteral _ | ENonLinBinOp _ | ENonLinUnOp _ ->
        envt, CEmpty, e, empty_expr 
    | EVar v ->
        (match try find_type envt v with Not_found -> failwith"6'" with
          | MultiValueType ([], _) ->
              envt, CEmpty, empty_expr , EVar v
          | _ -> envt, CEmpty, EVar v, empty_expr )
    | ELinAdd _ | ELinMul _ | ELinZero _ | Dup _ ->
        envt, CEmpty, empty_expr , e
    | ETuple [] ->
        envt, CEmpty, ETuple [], empty_expr 
    | ETuple (x::_) ->
        (match try find_type envt x with Not_found -> failwith"7'" with
          | MultiValueType ([], _) ->
              envt, CEmpty, empty_expr, e
          | _ -> envt, CEmpty, e, empty_expr)
    | EMultiValue (nlvs, lvs) ->
        envt, CEmpty, EMultiValue (nlvs, []), EMultiValue ([], lvs)
    | EDec (nlvs, nlts, lvs, lts, e1, e2) ->
        let envt = add_variable_types envt nlvs lvs nlts lts in
        let envt, c1, nle1, le1 = unzip env_fu envt e1 in
        let envt, c2, nle2, le2 = unzip env_fu envt e2 in
        let c = CDec (nlvs, nlts, [], [], nle1, CEmpty) in
        let c = compose_context c1 (compose_context c c2) in
        envt, c, nle2, EDec ([], [], lvs, lts, le1, le2)
    | ENonLinUnpack (vs, ts, v, e1) ->
        let envt = add_variable_types envt vs [] ts [] in
        let envt, c, nle, le = unzip env_fu envt e1 in
        let c' = CNonLinUnpack (vs, ts, v, CEmpty) in
        let c' = compose_context c' c in
        envt, c', nle, le
    | ELinUnpack (vs, ts, v, e1) ->
        let envt = add_variable_types envt [] vs [] ts in
        let envt, c, nle, le = unzip env_fu envt e1 in
        envt, c, nle, ELinUnpack (vs, ts, v, le)
    | EFunCall (f, nlvs, lvs) ->
        let (nlf, nlts1, lf, nlts2) = try Environnement.find f env_fu with Not_found -> failwith"11'" in
        let nlvs1, nlvs2 = fresh_var nlts1, fresh_var nlts2 in
        let envt = add_variable_types envt (nlvs2 @ nlvs1) [] (nlts2 @ nlts1) [] in
        let c = CDec (nlvs1 @ nlvs2, nlts1 @ nlts2, [], [], EFunCall (nlf, nlvs, []), CEmpty) in
        envt, c, EMultiValue (nlvs1, []), EFunCall (lf, nlvs2, lvs)
    | Drop e' ->
        let envt, c, e1, e2 = unzip env_fu envt e' in
        envt, c, Drop e1, Drop e2

(* Unzip a program *)
let unzip_prog (p : prog) : prog * prog =
    let rec aux (env_fu : environnementFunctionUnzipping) (env_ft : environnementFunctionTypes) (p : prog) : prog * prog =
      match p with
        | [] -> [], []
        | (FunDec (f, nlvs, nlts, lvs, lts, e))::q ->
          let fnonlin, flin = f ^ "'nonlin", f ^ "'lin" in
          let env = add_variable_types { env_nlt = Environnement.empty; env_lt = Environnement.empty; env_ft = env_ft } nlvs lvs nlts lts in
          let _, MultiValueType (nlts', lts') = type_checker env e in
          let env_ft = Environnement.add f (nlts, lts, MultiValueType (nlts', lts')) env_ft in
          let envt, c, nle, le = unzip env_fu env e in
          let vs = free_non_linear_variables env le in
          let ts = try type_list envt vs with Not_found -> failwith"12" in
          let _, nle = add_nl_output env (fill_context c nle) vs in
          let env_fu = Environnement.add f (fnonlin, nlts', flin, ts) env_fu in
          let p1, p2 = aux env_fu env_ft q in
          (FunDec (f ^ "'nonlin", nlvs, nlts, [], [], nle))::p1, (FunDec (f ^"'lin", vs, ts, lvs, lts, le))::p2
    in aux Environnement.empty Environnement.empty p