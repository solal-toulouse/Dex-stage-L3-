open Syntax

let rec print_multivalue_type (mvt : multivalue_type) =
  let MultiValueType (lvs, nlvs) = mvt in
  Printf.fprintf stderr "(";
  print_value_type_list lvs;
  Printf.fprintf stderr "; ";
  print_value_type_list nlvs;
  Printf.fprintf stderr ")"

and print_value_type_list (l : value_type list) =
  match l with
    | [] -> ()
    | t::[] ->
      print_value_type t
    | t::q ->
      print_value_type t;
      Printf.fprintf stderr ",";
      print_value_type_list q

and print_value_type (v : value_type) =
  match v with
  | R ->
    Printf.fprintf stderr "real"

let empty_environnementTypes () =
  { env_nlt = Environnement.empty; env_lt = Environnement.empty; env_ft = Environnement.empty }

let print_env_type (env : environnementTypes) =
  let env_nlt, env_lt = env.env_nlt, env.env_lt in
  let l1, l2 = Environnement.bindings env_nlt, Environnement.bindings env_lt in
  let rec aux l = match l with
    | [] -> ()
    | (k, t)::q ->
      Printf.fprintf stderr "%s : " k;
      print_value_type t;
      Printf.fprintf stderr "\n";
      aux q
  in Printf.fprintf stderr "non linear : \n";
  aux l1;
  Printf.fprintf stderr "linear : \n";
  aux l2

let add_variable_types (env : environnementTypes) (nlvs : var list) (lvs : var list) (nlts : value_type list) (lts : value_type list) : environnementTypes =
  let env_nlt, env_lt, env_ft = env.env_nlt, env.env_lt, env.env_ft in
  let rec aux vs ts env_t =
    match vs, ts with
      | [], [] -> env_t
      | [], _| _, [] -> failwith"type error"
      | a::b, c::d ->
        let new_env_t = Environnement.add a c env_t in
        aux b d new_env_t
  in { env_nlt = aux nlvs nlts env_nlt; env_lt = aux lvs lts env_lt; env_ft = env_ft }

let find_type (env : environnementTypes) (v : var) : multivalue_type =
  try
    let t = Environnement.find v env.env_nlt in
    MultiValueType ([t], [])
  with
    Not_found -> 
      let t = Environnement.find v env.env_lt in
      MultiValueType ([], [t])

let read_type_variable (env : environnementTypes) (v : var) : environnementTypes * multivalue_type =
  match find_type env v with
    | MultiValueType ([t], []) -> env, MultiValueType ([t], [])
    | MultiValueType ([], [t]) ->
      let new_env_lt = Environnement.remove v env.env_lt in
      { env_nlt = env.env_nlt; env_lt = new_env_lt; env_ft = env.env_ft }, MultiValueType ([], [t])
    | _ -> failwith"something else than a variable used like a variable"

let read_types (env : environnementTypes) (nlvs : var list) (lvs : var list) : environnementTypes * multivalue_type =
  let rec aux (env : environnementTypes) (vs : var list) : environnementTypes * value_type list =
    match vs with
      | [] -> env, []
      | v::q ->
          let new_env, mvt = read_type_variable env v in
          let t = (match mvt with
            | MultiValueType ([t'], []) -> t'
            | MultiValueType ([], [t']) -> t'
            | _ -> failwith "something else than a variable used like a variable") in
          let new_env2, ts = aux new_env q
          in new_env2, t::ts
  in let new_env, nlts = aux env nlvs
  in let new_env2, lts = aux new_env lvs in
  new_env2, MultiValueType (nlts, lts)

let verif_type_nonlin_binop (env : environnementTypes) (v1 : var) (v2 : var) : multivalue_type =
  let t1, t2 = find_type env v1, find_type env v2 in
  match t1, t2 with
    | MultiValueType ([R], []), MultiValueType ([R], []) -> MultiValueType ([R], [])
    | _ -> failwith"binary operation between different types"

let verif_type_nonlin_unop (env : environnementTypes) (v : var) : multivalue_type =
    match find_type env v with
        | MultiValueType ([R], []) -> MultiValueType ([R], [])
        | _ -> failwith"unary operator applied to something else than a float"
    
let verif_type_list (nlt1s : value_type list) (lt1s : value_type list) (mvt : multivalue_type) : unit =
  let MultiValueType (nlt2s, lt2s) = mvt in
  let rec aux t1s t2s =
    match t1s, t2s with
      | [], [] -> ()
      | _, [] | [], _ -> failwith"wrong number of arguments"
      | t1::q1, t2::q2 when t1 = t2 -> aux q1 q2
      | _ -> failwith"wrong type"
  in aux nlt1s nlt2s;
  aux lt1s lt2s

let verif_type_lin_add (env : environnementTypes) (v1 : var) (v2 : var) : multivalue_type =
  let mvt1, mvt2 = find_type env v1, find_type env v2 in
  match mvt1, mvt2 with
    | MultiValueType ([], [R]), MultiValueType ([], [R]) -> MultiValueType ([], [R])
    | _ -> failwith"binary operation between different types"

let verif_type_lin_mul (env : environnementTypes) (v1 : var) (v2 : var) : multivalue_type =
  let t1, t2 = find_type env v1, find_type env v2 in
  match t1, t2 with
    | MultiValueType ([R], []), MultiValueType ([], [R]) -> MultiValueType ([], [R])
    | _ -> failwith"binary operation between unauthorized types"

let rec type_checker (env : environnementTypes) (e : expr) : environnementTypes * multivalue_type =
  match e with
    | EMultiValue (nlvs, lvs) -> read_types env nlvs lvs
    | EDec (nlvs, nlts, lvs, lts, e1, e2) ->
      let new_env = add_variable_types env nlvs lvs nlts lts in
      let new_env2, mvt = type_checker new_env e1
      in verif_type_list nlts lts mvt;
      type_checker new_env2 e2
    | EFunCall (f, nlv1s, lv1s) ->
      let nlt2s, lt2s, mv2t = Environnement.find f env.env_ft in
      let new_env, mv1t = read_types env nlv1s lv1s in
      verif_type_list nlt2s lt2s mv1t;
      new_env, mv2t
    | ENonLinLiteral _ -> env, MultiValueType ([R], [])
    | EVar v ->
      read_type_variable env v
    | ENonLinBinOp (v1, _, v2) -> 
      env, verif_type_nonlin_binop env v1 v2
    | ENonLinUnOp (_, v) ->
      env, verif_type_nonlin_unop env v
    | ELinAdd (v1, v2) ->
    let mvt = verif_type_lin_add env v1 v2 in
    let new_env, _ = read_type_variable env v1 in
    let new_env2, _ = read_type_variable new_env v2 in
    new_env2, mvt
    | ELinMul (v1, v2) ->
    let mvt = verif_type_lin_mul env v1 v2 in
    let new_env, _ = read_type_variable env v1 in
    let new_env2, _ = read_type_variable new_env v2 in
    new_env2, mvt
    | ELinZero t -> env, MultiValueType ([], [t])
    | Dup v -> 
      (match read_types env [] [v] with
        | new_env, MultiValueType ([], [t]) ->
            new_env, MultiValueType ([], [t; t])
        | _ -> failwith"dup operator used on something else than a linary variable")
    | Drop v ->
      (match read_types env [] [v] with
        | new_env, MultiValueType ([], [_]) ->
            new_env, MultiValueType ([], [])
        | _ -> failwith"dup operator used on something else than a linary variable")

let is_empty (env : environnementTypes) : bool =
  Environnement.is_empty env.env_lt

let type_checker_function (env_ft : environnementFunctionTypes) (nlvs : var list) (lvs : var list) (nlts : value_type list) (lts : value_type list) (e : expr) : multivalue_type =
  let env = { env_nlt = Environnement.empty; env_lt = Environnement.empty; env_ft = env_ft } in
  let new_env = add_variable_types env nlvs lvs nlts lts in
  let new_env2, mvt = type_checker new_env e
  in if is_empty new_env2 then
    mvt
  else
    failwith"unused linear variable"

let rec interpret_type (env_ft : environnementFunctionTypes) (p : prog) : multivalue_type =
  match p with
    | [] -> failwith"empty program"
    | [FunDec ("main", [], [], [], [], e)] ->
      let env, mvt = type_checker { env_nlt = Environnement.empty; env_lt = Environnement.empty; env_ft = env_ft } e in
      if (is_empty env) then
        mvt
      else
        failwith"unused linear variable"
    | (FunDec (f, nlvs, nlts, lvs, lts, e))::q ->
      let mvt = type_checker_function env_ft nlvs lvs nlts lts e in
      let new_env_ft = Environnement.add f (nlts, lts, mvt) env_ft in
      interpret_type new_env_ft q
