open Syntax
open Transposition
(* open Print *)

let rec add_list (env : 'a Environnement.t) (vs : var list) (ts : 'a list) : 'a Environnement.t =
    match vs, ts with
        | [], [] -> env
        | v::vq, t::tq -> add_list (Environnement.add v t env) vq tq
        | _ -> failwith"weird"

(* Returns the list of the types of a list of expressions *)
let rec high_type_list (env : value_type Environnement.t) (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (es : expr_hl list) : value_type Environnement.t * value_type list =
    match es with
        | [] -> env, []
        | e::q ->
            let env, HLMultiValueType ts = high_type_checker env envf e in
            match ts with
                | [t] ->
                    let env, ts = high_type_list env envf q in
                    env, t::ts
                | _ -> failwith"multireturn expression used as an simple expression"

(* The type checker for our high level language *)
and high_type_checker (env : value_type Environnement.t) (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (e : expr_hl) : value_type Environnement.t * multivalue_type_hl =
    match e with
        | HLLiteral _ -> env, HLMultiValueType [Real]
        | HLVar v -> env, HLMultiValueType (try [Environnement.find v env] with Not_found -> failwith"1.")
        | HLBinOp (e1, _, e2) ->
            let env, t1 = high_type_checker env envf e1 in
            let env, t2 = high_type_checker env envf e2 in
            if (t1 = t2) then env, t1 else failwith"wrong type"
        | HLUnOp (_, e') ->
            high_type_checker env envf e'
        | HLTuple [] ->
            env, HLMultiValueType ([Tuple []])
        | HLTuple es ->
            let env, ts = high_type_list env envf es in
            env, HLMultiValueType ([Tuple ts])
        | HLMultiValue es ->
            let env, ts = high_type_list env envf es in
            env, HLMultiValueType ts
        | HLLet (vs, ts, e1, e2) ->
            let env, HLMultiValueType ts' = high_type_checker env envf e1 in
            if ts = ts' then
            (let env = add_list env vs ts in
            high_type_checker env envf e2)
            else failwith"type error"
        | HLUnpack (vs, ts, e1, e2) ->
            let env, HLMultiValueType ts' = high_type_checker env envf e1 in
            if [Tuple ts] = ts' then
            (let env = add_list env vs ts in
            high_type_checker env envf e2)
            else failwith"type error"
        | HLFunCall (f, es) ->
            let ts, mvt = try Environnement.find f envf with Not_found -> failwith"2." in
            let env, ts' = high_type_list env envf es in
            if ts = ts' then env, mvt
            else failwith"type error"

(* Traduce the high level language to Linear A *)
let rec translate (env : value_type Environnement.t) (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (e : expr_hl) : value_type Environnement.t * expr =
  match e with
    | HLLiteral r -> env, ENonLinLiteral r
    | HLVar v -> env, EVar v
    | HLBinOp (e1, op, e2) ->
        let v1, v2 = two_fresh_var [Real; Real] in
        let env, e1' = translate env envf e1 in
        let env, e2' = translate env envf e2 in
        env, ELet ([v1], [Real], [], [], e1', ELet ([v2], [Real], [], [], e2', ENonLinBinOp (v1, op, v2)))
    | HLUnOp (op, e') ->
        let v = one_fresh_var [Real] in
        let env, e'' = translate env envf e' in
        env, ELet ([v], [Real], [], [], e'', ENonLinUnOp (op, v))
    | HLTuple [] ->
        env, ETuple []
    | HLTuple es ->
        let env, ts = high_type_list env envf es in
        let vs = fresh_var ts in
        let e' = ETuple vs in
        translate_list env envf es vs e'
    | HLMultiValue es ->
        let env, ts = high_type_list env envf es in
        let vs = fresh_var ts in
        let e' = EMultiValue (vs, []) in
        translate_list env envf es vs e'
    | HLLet (vs, ts, e1, e2) ->
        let env, e1' = translate env envf e1 in
        let env = add_list env vs ts in
        let env, e2' = translate env envf e2 in
        env, ELet (vs, ts, [], [], e1', e2')
    | HLUnpack (vs, ts, e1, e2) ->
        let env, e1' = translate env envf e1 in
        let env = add_list env vs ts in
        let v = one_fresh_var [Tuple ts] in
        let env, e2' = translate env envf e2 in
        env, ELet ([v], [Tuple ts], [], [], e1', ENonLinUnpack (vs, ts, v, e2'))
    | HLFunCall (f, es) ->
        let env, ts = high_type_list env envf es in
        let vs = fresh_var ts in
        let e' = EFunCall (f, vs, []) in
        translate_list env envf es vs e'

and translate_list (env : value_type Environnement.t) (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (es : expr_hl list) (vs : var list) (e : expr): value_type Environnement.t * expr =
    match es, vs with
        | [], [] -> env, e
        | e1::eq, v1::vq ->
            let env, e1' = translate env envf e1 in
            let env, HLMultiValueType ts1 = high_type_checker env envf e1 in
            let t1 = List.hd ts1 in
            let env, e' = translate_list env envf eq vq e in
            env, ELet ([v1], [t1], [], [], e1', e')
        | _ -> failwith"weird"

let rec translate_prog (envf : ((value_type list) * multivalue_type_hl) Environnement.t) (p : prog_hl) : prog =
    match p with
        | [] -> []
        | (HLFunDec (f, vs, ts, e))::q ->
            let env = add_list Environnement.empty vs ts in
            let _, mvt = high_type_checker env envf e in
            let envf = Environnement.add f (ts, mvt) envf in
            let _, e' = translate env envf e in
            (FunDec (f, vs, ts, [], [], e'))::(translate_prog envf q)

let rec var_list_to_expr_hl_list (vs : var list) : expr_hl list =
    match vs with
        | [] -> []
        | v::vq -> (HLVar v)::(var_list_to_expr_hl_list vq)

let rec find_expr_of_var (vs : var list) (es : expr_hl list) (v : var) : expr_hl =
    match vs, es with
        | [], [] -> HLVar v
        | v'::_, e::_ when v = v' -> e
        | _::vq, _::eq -> find_expr_of_var vq eq v
        | _ -> failwith"weird"

let rec nb_occurence_list (es : expr_hl list) (v : var) : int =
    match es with
    | [] -> 0
    | e::eq ->
        (nb_occurence e v) + (nb_occurence_list eq v)

and nb_occurence (e : expr_hl) (v : var) : int =
    match e with
    | HLVar v' ->
        (if v = v' then 1 else 0)
    | HLBinOp (e1, _, e2) ->
        (nb_occurence e1 v) + (nb_occurence e2 v)
    | HLUnOp (_, e') ->
        nb_occurence e' v
    | HLTuple es ->
        nb_occurence_list es v
    | HLMultiValue es ->
        nb_occurence_list es v
    | HLLet (_, _, e1, e2) ->
        nb_occurence e1 v + nb_occurence e2 v
    | HLUnpack (_, _, e1, e2) ->
        nb_occurence e1 v + nb_occurence e2 v
    | HLFunCall (_, es) ->
        nb_occurence_list es v
    | _ -> 0

let rec replace (e : expr_hl) (vs : var list) (es : expr_hl list) : expr_hl =
    match e with
        | HLVar v ->
            find_expr_of_var vs es v
        | HLBinOp (e1, op, e2) ->
            let e1', e2' = replace e1 vs es, replace e2 vs es in
            HLBinOp (e1', op, e2')
        | HLUnOp (op, e') ->
            let e'' = replace e' vs es in
            HLUnOp (op, e'')
        | HLTuple es' ->
            let es'' = replace_list es' vs es in
            HLTuple es''
        | HLMultiValue es' ->
            let es'' = replace_list es' vs es in
            HLMultiValue es''
        | HLLet (vs', ts, e1, e2) ->
            let e1', e2' = replace e1 vs es, replace e2 vs es in
            HLLet (vs', ts, e1', e2')
        | HLUnpack (vs', ts, e1, e2) ->
            let e1', e2' = replace e1 vs es, replace e2 vs es in
            HLUnpack (vs', ts, e1', e2')
        | HLFunCall (f, es') ->
            let es'' = replace_list es' vs es in
            HLFunCall (f, es'') 
        | _ -> e

and replace_list (es' : expr_hl list) (vs : var list) (es : expr_hl list) : expr_hl list =
    match es' with
        | [] -> []
        | e::eq -> (replace e vs es)::(replace_list eq vs es)

let rec used_once (e : expr_hl) (vs : var list) (ts : value_type list) (es : expr_hl list): var list * expr_hl list * var list * value_type list * expr_hl list =
    match vs, ts, es with
        | [], [], [] -> [], [], [], [], []
        | v::vq, _::tq, e'::eq when nb_occurence e v != 1 ->
            let vs1, es1, vs2, ts2, es2 = used_once e vq tq eq in
            v::vs1, e'::es1, vs2, ts2, es2
        | v::vq, t::tq, e'::eq ->
            let vs1, es1, vs2, ts2, es2 = used_once e vq tq eq in
            vs1, es1, v::vs2, t::ts2, e'::es2
        | _ -> failwith"weird"

let rec compress (e : expr) : expr_hl =
  match e with
    | ENonLinLiteral f -> HLLiteral f
    | EVar v -> HLVar v
    | ENonLinBinOp (v1, op, v2) -> HLBinOp (HLVar v1, op, HLVar v2)
    | ENonLinUnOp (op, v) -> HLUnOp (op, HLVar v)
    | ELinAdd (v1, v2) -> HLBinOp (HLVar v1, OpPlus, HLVar v2)
    | ELinMul (v1, v2) -> HLBinOp (HLVar v1, OpTimes, HLVar v2)
    | ETuple vs -> HLTuple (var_list_to_expr_hl_list vs)
    | ELinZero _ -> HLLiteral 0.
    | EMultiValue (nlvs, lvs) -> HLMultiValue (var_list_to_expr_hl_list (nlvs @ lvs))
    | ELet (nlvs, nlts, lvs, lts, e1, e2) ->
        let e1' = compress e1 in
        let e2' = compress e2 in
        (match e1' with 
            | HLLet _ ->
                HLLet (nlvs @ lvs, nlts @ lts, e1', e2')
            | _ ->
                let es = (match e1' with | HLMultiValue es' -> es' | _ -> [e1']) in
                print_int (List.length (nlvs @ lvs));
                print_string " ";
                print_int (List.length es);
                print_string "\n";
                let vs1, es1, vs2, ts2, es2 = used_once e2' (nlvs @ lvs) (nlts @ lts) es in
                if vs2 != [] then
                HLLet (vs2, ts2, HLMultiValue es2, (replace e2' vs1 es1))
                else replace e2' vs1 es1)
    | ENonLinUnpack (vs, ts, v, e') -> HLUnpack (vs, ts, HLVar v, compress e')
    | ELinUnpack (vs, ts, v, e') -> HLUnpack (vs, ts, HLVar v, compress e')
    | EFunCall (f, nlvs, lvs) -> HLFunCall (f, var_list_to_expr_hl_list (nlvs @ lvs))
    | Dup v -> HLMultiValue [HLVar v; HLVar v]
    | Drop _ -> HLMultiValue []

let rec compress_prog (p : prog) : prog_hl =
    match p with
        | [] -> []
        | (FunDec (f, nlvs, nlts, lvs, lts, e))::pq ->
            (HLFunDec (f, nlvs @ lvs, nlts @ lts, compress e))::(compress_prog pq)