open Syntax
(* open Print *)

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
  let f = try Environnement.find v indice with Not_found -> failwith"a'" in
  let i = f () in
  let v' = v ^ (if i = 1 then "" else "-" ^ (string_of_int i)) in
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

(* Replaces redefinition of variables by definitions of new ones in a expression *)
(* 'indice' contains for each name of variables function which gives a fresh indice *)
(* 'renaming' contains for each variable the name of the variable which replaces it *)
let rec rename_variables (renaming : var Environnement.t) (indice : (unit -> int) Environnement.t) (e : expr) : var Environnement.t * (unit -> int) Environnement.t * expr =
  match e with
    | ENonLinLiteral _ -> renaming, indice, e
    | EVar v ->
        let v' = try Environnement.find v renaming with Not_found -> failwith"c'"
        in renaming, indice, EVar v'
    | ENonLinBinOp (v1, op, v2) ->
        let v1', v2' = (try Environnement.find v1 renaming with Not_found -> failwith"d'"), try Environnement.find v2 renaming with Not_found -> failwith"e'" in
        renaming, indice, ENonLinBinOp (v1', op, v2')
    | ENonLinUnOp (op, v) ->
        let v' = try Environnement.find v renaming with Not_found -> failwith"f'" in
        renaming, indice, ENonLinUnOp (op, v')
    | ELinAdd (v1, v2) ->
        let v1', v2' = (try Environnement.find v1 renaming with Not_found -> failwith"g'"), try Environnement.find v2 renaming with Not_found -> failwith"h'"in
        renaming, indice, ELinAdd (v1', v2')
    | ELinMul (v1, v2) ->
        let v1', v2' = (try Environnement.find v1 renaming with Not_found -> failwith"i'"), try Environnement.find v2 renaming with Not_found -> failwith"j'"in
        renaming, indice, ELinMul (v1', v2')
    | ETuple vs ->
        renaming, indice, ETuple (try current_name renaming vs with Not_found -> failwith"b'")
    | ELinZero _ -> renaming, indice, e
    | EMultiValue (nlvs, lvs) ->
        renaming, indice, EMultiValue ((try current_name renaming nlvs with Not_found -> failwith"n'"), try current_name renaming lvs with Not_found -> failwith"o'")
    | ELet (nlvs, nlts, lvs, lts, e1, e2) ->
        let renaming, indice, e1' = rename_variables renaming indice e1 in
        let renaming, indice, nlvs' = fresh_name_list renaming indice nlvs in
        let renaming, indice, lvs' = fresh_name_list renaming indice lvs in
        let renaming, indice, e2' = rename_variables renaming indice e2 in
        renaming, indice, ELet (nlvs', nlts, lvs', lts, e1', e2')
    | ENonLinUnpack (vs, ts, v, e) ->
        let v' = try Environnement.find v renaming with Not_found -> failwith"k'"in
        let renaming, indice, vs' = fresh_name_list renaming indice vs in
        let renaming, indice, e' = rename_variables renaming indice e in
        renaming, indice, ENonLinUnpack (vs', ts, v', e')
    | ELinUnpack (vs, ts, v, e) ->
        let v' = try Environnement.find v renaming with Not_found -> failwith"l'" in
        let renaming, indice, vs' = fresh_name_list renaming indice vs in
        let renaming, indice, e' = rename_variables renaming indice e in
        renaming, indice, ELinUnpack (vs', ts, v', e')
    | EFunCall (f, nlvs, lvs) ->
        let nlvs', lvs' = (try current_name renaming nlvs with Not_found -> failwith"p'"), try current_name renaming lvs with Not_found -> failwith"q'" in
        let fs = try current_name renaming [f] with Not_found -> failwith"r'" in
        (match fs with
            | [f'] -> renaming, indice, EFunCall (f', nlvs', lvs')
            | _ -> failwith"weird")
    | Dup v ->
        renaming, indice, Dup (try Environnement.find v renaming with Not_found -> failwith"m'")
    | Drop e ->
        let renaming, indice, e' = rename_variables renaming indice e in
        renaming, indice, Drop e'

(* Replaces redefinition of variables by definitions of new ones in a program *)
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

let rec new_var (vs : var list) (vs' : var list) (v : var) : var =
  match vs, vs' with
    | [], [] -> v
    | v1::_, v2::_ when v1 = v -> v2
    | _::q1, _::q2 -> new_var q1 q2 v
    | _ -> failwith"error simplification"

let rec new_var_list (vs1 : var list) (vs2 : var list) (vs : var list) : var list =
  match vs with
    | [] -> []
    | v::q -> (new_var vs1 vs2 v)::(new_var_list vs1 vs2 q)

(* Replaces the variable of 'vs1' by the ones of 'vs2' in 'e' *)
let rec replace (vs1 : var list) (vs2 : var list) (e : expr) : expr =
  match e with
  | ENonLinLiteral _ -> e
  | ENonLinBinOp (v1, op, v2) ->
      let v1', v2' = new_var vs1 vs2 v1, new_var vs1 vs2 v2 in
      ENonLinBinOp (v1', op, v2')
  | ENonLinUnOp (op, v) ->
      let v' = new_var vs1 vs2 v in
      ENonLinUnOp (op, v')
  | EVar v -> EVar (new_var vs1 vs2 v)
  | ELinAdd (v1, v2) ->
      let v1', v2' = new_var vs1 vs2 v1, new_var vs1 vs2 v2 in
      ELinAdd (v1', v2')
  | ELinZero _ -> e
  | Dup v -> Dup (new_var vs1 vs2 v)
  | ELinMul (v1, v2) ->
      let v1', v2' = new_var vs1 vs2 v1, new_var vs1 vs2 v2 in
      ELinMul (v1', v2')
  | ETuple vs ->
      let vs' = new_var_list vs1 vs2 vs in
      ETuple vs'
  | EMultiValue (nlvs2, lvs2) ->
      let nlvs2' = new_var_list vs1 vs2 nlvs2
      and lvs2' = new_var_list vs1 vs2 lvs2 in
      EMultiValue (nlvs2', lvs2')
  | EFunCall (f, nlvs2, lvs2) ->
      let nlvs2' = new_var_list vs1 vs2 nlvs2
      and lvs2' = new_var_list vs1 vs2 lvs2 in
      EFunCall (f, nlvs2', lvs2')
  | ELet (nlvs, nlts, lvs, lts, e1, e2) ->
      let e1' = replace vs1 vs2 e1 in
      ELet (nlvs, nlts, lvs, lts, e1', replace vs1 vs2 e2)
  | ENonLinUnpack (vs, ts, v, e') ->
      ENonLinUnpack (vs, ts, new_var vs1 vs2 v, replace vs1 vs2 e')
  | ELinUnpack (vs, ts, v, e') ->
      ELinUnpack (vs, ts, new_var vs1 vs2 v, replace vs1 vs2 e')
  | Drop e' -> Drop (replace vs1 vs2 e')

(* Deletes 'let (;) = (;) in ...' and 'let (x1, x2, ...) = (y1, y2, ...) in ...' *)
let rec simplify (e : expr) : expr =
  match e with
    | ELet ([], [], [], [], EMultiValue ([], []), e') -> simplify e'
    | ELet ([], [], [], [], Drop e', EMultiValue ([], [])) -> Drop (simplify e')
    | ELet (nlvs, _, lvs, _, EMultiValue (nlvs', lvs'), e') ->
        simplify (replace (nlvs @ lvs) (nlvs' @ lvs') e')
    | ELet (nlvs, _, lvs, _, e', EMultiValue (nlvs', lvs')) when nlvs = nlvs' && lvs = lvs' -> simplify e'
    | ELet ([v], _, [], _, e', EVar v') when v = v' -> simplify e'
    | ELet ([], _, [v], _, e', EVar v') when v = v' -> simplify e'
    | ELet (nlvs, _, lvs, _, EVar v, e') ->
        simplify (replace (nlvs @ lvs) [v] e')
    | ENonLinUnpack ([], [], _, e') -> simplify e'
    | ELinUnpack ([], [], _, e') -> simplify e'
    | ENonLinUnpack (vs, ts, v, e') ->
        ENonLinUnpack (vs, ts, v, simplify e')
    | ELet (nlvs, nlts, lvs, lts, e1, e2) -> 
        ELet (nlvs, nlts, lvs, lts, simplify e1, simplify e2)
    | ELinUnpack (vs, ts, v, e') ->
        ELinUnpack (vs, ts, v, simplify e')
    | Drop e' ->
        Drop (simplify e')
    | _ -> e

(* Just deletes let (;) = (;) in ... *)
let rec simplify2 (e : expr) : expr =
  match e with
    | ELet ([], [], [], [], EMultiValue ([], []), e') -> simplify2 e'
    | ELet ([], [], [], [], Drop e', EMultiValue ([], [])) -> Drop (simplify2 e')
    | ENonLinUnpack ([], [], _, e') -> simplify2 e'
    | ELinUnpack ([], [], _, e') -> simplify2 e'
    | ENonLinUnpack (vs, ts, v, e') ->
        ENonLinUnpack (vs, ts, v, simplify2 e')
    | ELet (nlvs, nlts, lvs, lts, e1, e2) -> 
        ELet (nlvs, nlts, lvs, lts, simplify2 e1, simplify2 e2)
    | ELinUnpack (vs, ts, v, e') ->
        ELinUnpack (vs, ts, v, simplify2 e')
    | Drop e' ->
        Drop (simplify2 e')
    | _ -> e


(* Simplifies a program with the previous transformations *)
let simplify_prog (p : prog) : prog =
  let _, _, p' = rename_variables_prog Environnement.empty Environnement.empty p in
  let rec aux (p : prog) : prog =
  match p with
    | [] -> []
    | (FunDec (f, nlvs, nlts, lvs, lts, e))::q ->
        let e' = simplify e in
        (FunDec (f, nlvs, nlts, lvs, lts, e'))::(aux q)
  in aux p'

let simplify_prog2 (p : prog) : prog =
  let _, _, p' = rename_variables_prog Environnement.empty Environnement.empty p in
  let rec aux (p : prog) : prog =
  match p with
    | [] -> []
    | (FunDec (f, nlvs, nlts, lvs, lts, e))::q ->
        let e' = simplify2 e in
        (FunDec (f, nlvs, nlts, lvs, lts, e'))::(aux q)
  in aux p'
