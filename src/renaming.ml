open Syntax

let counter () =
  let i = ref 0 in
  let f () =
    incr i; !i
  in f

let fresh_name (renaming : var Environnement.t) (indice : (unit -> int) Environnement.t) (v : var)  : (var Environnement.t) * ((unit -> int) Environnement.t) * var =
  let indice =
    (if not (Environnement.mem v indice) then
      Environnement.add v (counter ()) indice
    else indice) in
  let f = Environnement.find v indice in
  let i = f () in
  let v' = v ^ (if i = 1 then "" else (string_of_int i)) in
  let renaming = Environnement.add v v' renaming in
  renaming, indice, v'

let rec fresh_name_list (renaming : var Environnement.t) (indice : (unit -> int) Environnement.t) (vs : var list) : (var Environnement.t) * ((unit -> int) Environnement.t) * var list =
  match vs with
    | [] -> renaming, indice, []
    | v::q ->
        let renaming, indice, v' = fresh_name renaming indice v in
        let renaming, indice, q' = fresh_name_list renaming indice q in
        renaming, indice, v'::q'

let rec current_name (renaming : var Environnement.t) (vs: var list) : var list =
  match vs with
    | [] -> []
    | v::q ->
        let v' = Environnement.find v renaming in
        v'::(current_name renaming q)

let rec rename_variables (renaming : var Environnement.t) (indice : (unit -> int) Environnement.t) (e : expr) : var Environnement.t * (unit -> int) Environnement.t * expr =
  match e with
    | ENonLinLiteral _ -> renaming, indice, e
    | EVar v ->
        let v' = Environnement.find v renaming
        in renaming, indice, EVar v'
    | ENonLinBinOp (v1, op, v2) ->
        let v1', v2' = Environnement.find v1 renaming, Environnement.find v2 renaming in
        renaming, indice, ENonLinBinOp (v1', op, v2')
    | ENonLinUnOp (op, v) ->
        let v' = Environnement.find v renaming in
        renaming, indice, ENonLinUnOp (op, v')
    | ELinAdd (v1, v2) ->
        let v1', v2' = Environnement.find v1 renaming, Environnement.find v2 renaming in
        renaming, indice, ELinAdd (v1', v2')
    | ELinMul (v1, v2) ->
        let v1', v2' = Environnement.find v1 renaming, Environnement.find v2 renaming in
        renaming, indice, ELinMul (v1', v2')
    | ETuple vs ->
        renaming, indice, ETuple (current_name renaming vs)
    | ELinZero _ -> renaming, indice, e
    | EMultiValue (nlvs, lvs) ->
        renaming, indice, EMultiValue (current_name renaming nlvs, current_name renaming lvs)
    | EDec (nlvs, nlts, lvs, lts, e1, e2) ->
        let renaming, indice, e1' = rename_variables renaming indice e1 in
        let renaming, indice, nlvs' = fresh_name_list renaming indice nlvs in
        let renaming, indice, lvs' = fresh_name_list renaming indice lvs in
        let renaming, indice, e2' = rename_variables renaming indice e2 in
        renaming, indice, EDec (nlvs', nlts, lvs', lts, e1', e2')
    | ENonLinUnpack (vs, ts, v, e) ->
        let v' = Environnement.find v renaming in
        let renaming, indice, vs' = fresh_name_list renaming indice vs in
        let renaming, indice, e' = rename_variables renaming indice e in
        renaming, indice, ENonLinUnpack (vs', ts, v', e')
    | ELinUnpack (vs, ts, v, e) ->
        let v' = Environnement.find v renaming in
        let renaming, indice, vs' = fresh_name_list renaming indice vs in
        let renaming, indice, e' = rename_variables renaming indice e in
        renaming, indice, ELinUnpack (vs', ts, v', e')
    | EFunCall (f, nlvs, lvs) ->
        let nlvs', lvs' = current_name renaming nlvs, current_name renaming lvs in
        renaming, indice, EFunCall (f, nlvs', lvs')
    | Dup v ->
        renaming, indice, Dup (Environnement.find v renaming)
    | Drop e ->
        let renaming, indice, e' = rename_variables renaming indice e in
        renaming, indice, Drop e'

let rec rename_variables_prog (renaming : var Environnement.t) (indice : (unit -> int) Environnement.t) (p : prog) : var Environnement.t * (unit -> int) Environnement.t * prog =
  match p with
    | [] -> renaming, indice, []
    | (FunDec (f, nlvs, nlts, lvs, lts, e))::q ->
        let renaming, indice, nlvs' = fresh_name_list renaming indice nlvs in
        let renaming, indice, lvs' = fresh_name_list renaming indice lvs in
        let renaming, indice, f' = fresh_name renaming indice f in
        let renaming, indice, e' = rename_variables renaming indice e in
        let renaming, indice, q' = rename_variables_prog renaming indice q in
        renaming, indice, (FunDec (f', nlvs', nlts, lvs', lts, e'))::q'
