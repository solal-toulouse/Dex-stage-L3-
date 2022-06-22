open Syntax
open Transposition

let rec add_list (env : 'a Environnement.t) (vs : var list) (ts : 'a list) : 'a Environnement.t =
    match vs, ts with
        | [], [] -> env
        | v::vq, t::tq -> add_list (Environnement.add v t env) vq tq
        | _ -> failwith"weird"

let rec high_type_list (env : value_type Environnement.t) (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (es : expr_hl list) : value_type list =
    match es with
        | [] -> []
        | e::q ->
            let HLMultiValueType ts = high_type_checker env envf e in
            match ts with
                | [t] -> t::(high_type_list env envf q)
                | _ -> failwith"multireturn expression used as an simple expression"

and high_type_checker (env : value_type Environnement.t) (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (e : expr_hl) : multivalue_type_hl =
    match e with
        | HLLiteral _ -> HLMultiValueType [Real]
        | HLVar v -> HLMultiValueType ([Environnement.find v env])
        | HLBinOp (e1, _, e2) ->
            let t1 = high_type_checker env envf e1 in
            let t2 = high_type_checker env envf e2 in
            if (t1 = t2) then t1 else failwith"wrong type"
        | HLUnOp (_, e') ->
            high_type_checker env envf e'
        | HLTuple [] ->
            HLMultiValueType ([Tuple []])
        | HLTuple es ->
            HLMultiValueType ([Tuple (high_type_list env envf es)])
        | HLMultiValue es ->
            HLMultiValueType (high_type_list env envf es)
        | HLLet (vs, ts, e1, e2) ->
            let HLMultiValueType ts' = high_type_checker env envf e1 in
            if ts = ts' then
            (let env = add_list env vs ts in
            high_type_checker env envf e2)
            else failwith"type error"
        | HLUnpack (vs, ts, e1, e2) ->
            let HLMultiValueType ts' = high_type_checker env envf e1 in
            if [Tuple ts] = ts' then
            (let env = add_list env vs ts in
            high_type_checker env envf e2)
            else failwith"type error"
        | HLFunCall (f, es) ->
            let ts, mvt = Environnement.find f envf in
            let ts' = high_type_list env envf es in
            if ts = ts' then mvt
            else failwith"type error"

let rec translate (env : value_type Environnement.t) (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (e : expr_hl) : expr =
  match e with
    | HLLiteral r -> ENonLinLiteral r
    | HLVar v -> EVar v
    | HLBinOp (e1, op, e2) ->
        let v1, v2 = two_fresh_var [Real; Real] in
        ELet ([v1], [Real], [], [], translate env envf e1, ELet ([v2], [Real], [], [], translate env envf e2, ENonLinBinOp (v1, op, v2)))
    | HLUnOp (op, e') ->
        let v = one_fresh_var [Real] in
        ELet ([v], [Real], [], [], translate env envf e', ENonLinUnOp (op, v))
    | HLTuple [] ->
        ETuple []
    | HLTuple es ->
        let ts = high_type_list env envf es in
        let vs = fresh_var ts in
        let e' = ETuple vs in
        translate_list env envf es vs e'
    | HLMultiValue es ->
        let ts = high_type_list env envf es in
        let vs = fresh_var ts in
        let e' = EMultiValue (vs, []) in
        translate_list env envf es vs e'
    | HLLet (vs, ts, e1, e2) ->
        let e1' = translate env envf e1 in
        let env = add_list env vs ts in
        ELet (vs, ts, [], [], e1', translate env envf e2)
    | HLUnpack (vs, ts, e1, e2) ->
        let e1' = translate env envf e1 in
        let env = add_list env vs ts in
        let v = one_fresh_var [Tuple ts] in
        ELet ([v], [Tuple ts], [], [], e1', ENonLinUnpack (vs, ts, v, translate env envf e2))
    | HLFunCall (f, es) ->
        let ts = high_type_list env envf es in
        let vs = fresh_var ts in
        let e' = EFunCall (f, vs, []) in
        translate_list env envf es vs e'

and translate_list (env : value_type Environnement.t) (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (es : expr_hl list) (vs : var list) (e : expr): expr =
    match es, vs with
        | [], [] -> e
        | e1::eq, v1::vq ->
            let e1' = translate env envf e1 in
            let HLMultiValueType ts1 = high_type_checker env envf e1 in
            let t1 = List.hd ts1 in
            ELet ([v1], [t1], [], [], e1', translate_list env envf eq vq e)
        | _ -> failwith"weird"

let rec translate_prog (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (p : prog_hl) : prog =
    match p with
        | [] -> []
        | (HLFunDec (f, vs, ts, e))::q ->
            let env = add_list Environnement.empty vs ts in
            let e' = translate env envf e in
            (FunDec (f, vs, ts, [], [], e'))::(translate_prog envf q)