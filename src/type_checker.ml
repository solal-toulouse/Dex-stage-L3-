open Syntax
(* open Print *)

(* adds variables with their type to the environnement *)
let add_variable_types (env : environnementTypes) (nlvs : var list) (lvs : var list) (nlts : value_type list) (lts : value_type list) : environnementTypes =
  let env_nlt, env_lt, env_ft = env.env_nlt, env.env_lt, env.env_ft in
  let rec aux vs ts env_t =
    match vs, ts with
      | [], [] -> env_t
      | [], _| _, [] -> failwith"type error"
      | a::b, c::d ->
          let env_t = Environnement.add a c env_t in
          aux b d env_t
  in { env_nlt = aux nlvs nlts env_nlt; env_lt = aux lvs lts env_lt; env_ft = env_ft }

(* finds the type of a variable stored in the environnement *)
let find_type (env : environnementTypes) (v : var) : multivalue_type =
  try
    let t = Environnement.find v env.env_nlt in
    MultiValueType ([t], [])
  with
    Not_found -> 
      try
        let t = Environnement.find v env.env_lt in
        MultiValueType ([], [t])
      with
        Not_found -> failwith ("variable not found : " ^ v)

(* returns the type of a variable deleting it when it's a linear variable *)
let read_type_variable (env : environnementTypes) (v : var) : environnementTypes * multivalue_type =
  match find_type env v with
    | MultiValueType ([t], []) -> env, MultiValueType ([t], [])
    | MultiValueType ([], [t]) ->
      let env_lt = Environnement.remove v env.env_lt in
      { env_nlt = env.env_nlt; env_lt = env_lt; env_ft = env.env_ft }, MultiValueType ([], [t])
    | _ -> failwith(v ^ " hasn't the type of a variable")

(* returns the type of two list of variables using the previous function *)
let read_types (env : environnementTypes) (nlvs : var list) (lvs : var list) : environnementTypes * multivalue_type =
  let rec aux (env : environnementTypes) (vs : var list) : environnementTypes * value_type list =
    match vs with
      | [] -> env, []
      | v::q ->
          let env, mvt = read_type_variable env v in
          let t = (match mvt with
            | MultiValueType ([t'], []) -> t'
            | MultiValueType ([], [t']) -> t'
            | _ -> failwith(v ^ " hasn't the type of a variable")) in
          let env, ts = aux env q
          in env, t::ts
  in let env, nlts = aux env nlvs
  in let env, lts = aux env lvs in
  env, MultiValueType (nlts, lts)

(* same for a linear tuple *)
let rec read_tuple_type_lin (env : environnementTypes) (vs : var list) : environnementTypes * value_type =
    match vs with
      | [] -> env, Tuple []
      | v::q ->
        let x = Environnement.find v env.env_lt in
        let env_lt = Environnement.remove v env.env_lt in
        let env = { env_nlt = env.env_nlt; env_lt = env_lt; env_ft = env.env_ft } in
        (match read_tuple_type_lin env q with
          | env, Tuple xs ->
            env, Tuple (x::xs)
          | _ -> failwith"weird")
  
(* same for non linear tuple *)
let rec read_tuple_type_nonlin (env : environnementTypes) (vs : var list) : environnementTypes * value_type =
    match vs with
      | [] -> env, Tuple []
      | v::q ->
        let x = Environnement.find v env.env_nlt in
        (match read_tuple_type_nonlin env q with
          | _, Tuple xs ->
            env, Tuple (x::xs)
          | _ -> failwith"weird")

(* same for any tuple *)
let read_tuple_type (env : environnementTypes) (vs : var list) : environnementTypes * multivalue_type =
  try
    let env, t = read_tuple_type_lin env vs in
    env, MultiValueType ([], [t])
  with
    Not_found ->
      let env, t = read_tuple_type_nonlin env vs in
      env, MultiValueType ([t], [])

(* verifies if a non linear binary operation is allowed and returns its type *)
let verif_type_nonlin_binop (env : environnementTypes) (v1 : var) (v2 : var) : multivalue_type =
  let t1, t2 = find_type env v1, find_type env v2 in
  match t1, t2 with
    | MultiValueType ([Real], []), MultiValueType ([Real], []) -> MultiValueType ([Real], [])

    | _ -> failwith("binary operation between unauthorized types between " ^ v1 ^ " and " ^ v2)

(* verifies if a non linear unary operation is allowed and returns its type *)
let verif_type_nonlin_unop (env : environnementTypes) (v : var) : multivalue_type =
    match find_type env v with
        | MultiValueType ([Real], []) -> MultiValueType ([Real], [])
        | _ -> failwith("unary operator applied to something else than a real : " ^ v)
    
(* verifies is a multivalue type correspond to two type lists *)
let verif_type_list (nlt1s : value_type list) (lt1s : value_type list) (mvt : multivalue_type) : unit =
  let MultiValueType (nlt2s, lt2s) = mvt in
  let rec aux t1s t2s =
    match t1s, t2s with
      | [], [] -> ()
      | _, [] | [], _ -> failwith("wrong number of arguments")
      | t1::q1, t2::q2 when t1 = t2 -> aux q1 q2
      | _ -> failwith"wrong type"
  in aux nlt1s nlt2s;
  aux lt1s lt2s

(* verifies if the linear addition is allowed and returns its type *)
let verif_type_lin_add (env : environnementTypes) (v1 : var) (v2 : var) : multivalue_type =
  let mvt1, mvt2 = find_type env v1, find_type env v2 in
  match mvt1, mvt2 with
    | MultiValueType ([], [t]), MultiValueType ([], [t']) when t = t' -> MultiValueType ([], [t])
    | _ -> failwith("binary operation between unauthorized types between " ^ v1 ^ " and " ^ v2)

(* verifies if the linear multiplication is allowed and returns its type *)
let verif_type_lin_mul (env : environnementTypes) (v1 : var) (v2 : var) : multivalue_type =
  let t1, t2 = find_type env v1, find_type env v2 in
  match t1, t2 with
    | MultiValueType ([Real], []), MultiValueType ([], [Real]) -> MultiValueType ([], [Real])
    | _ -> failwith("binary operation between unauthorized types between " ^ v1 ^ " and " ^ v2)

(* removes a variable from the environnement *)
let remove_type (env : environnementTypes) (v : var) : environnementTypes =
    let env_nlt = Environnement.remove v env.env_nlt in
    let env_lt = Environnement.remove v env.env_lt in
    { env_nlt = env_nlt; env_lt = env_lt; env_ft = env.env_ft }

(* checks if the linear variables are used, and if it's not the case, returns the list of the unused variables *)
let rec are_variables_used (env_lt : environnementVariableTypes) (vs : var list) : var list =
  match vs with
    | [] -> []
    | v::q when Environnement.mem v env_lt -> v::(are_variables_used env_lt q)
    | _::q -> are_variables_used env_lt q

(* the main function, it returns the final environnement and the type of the result of an expression *)
let rec type_checker (env : environnementTypes) (e : expr) : environnementTypes * multivalue_type =
  match e with
    | EMultiValue (nlvs, lvs) -> read_types env nlvs lvs
    | EDec (nlvs, nlts, lvs, lts, e1, e2) ->
      let env, mvt = type_checker env e1 in
      let env = add_variable_types env nlvs lvs nlts lts in
      verif_type_list nlts lts mvt;
      let env, mvt = type_checker env e2 in
      (match (are_variables_used env.env_lt lvs) with
        | [] -> env, mvt
        | v::_ -> failwith("unused variable : " ^ v))
    | EFunCall (f, nlv1s, lv1s) ->
      let nlt2s, lt2s, mv2t = Environnement.find f env.env_ft in
      let env, mv1t = read_types env nlv1s lv1s in
      verif_type_list nlt2s lt2s mv1t;
      env, mv2t
    | ENonLinLiteral _ -> env, MultiValueType ([Real], [])
    | EVar v ->
      read_type_variable env v
    | ENonLinBinOp (v1, _, v2) -> 
      env, verif_type_nonlin_binop env v1 v2
    | ENonLinUnOp (_, v) ->
      env, verif_type_nonlin_unop env v
    | ELinAdd (v1, v2) ->
      let mvt = verif_type_lin_add env v1 v2 in
      let env, _ = read_type_variable env v1 in
      let env, _ = read_type_variable env v2 in
    env, mvt
    | ELinMul (v1, v2) ->
      let mvt = verif_type_lin_mul env v1 v2 in
      let env, _ = read_type_variable env v1 in
      let env, _ = read_type_variable env v2 in
      env, mvt
    | ELinZero t -> env, MultiValueType ([], [t])
    | Dup v -> 
      (match read_types env [] [v] with
        | env, MultiValueType ([], [t]) ->
            env, MultiValueType ([], [t; t])
        | _ -> failwith("dup operator used on something else than a linary variable : " ^ v))
    | Drop e ->
      let env, _ = type_checker env e in
        env, MultiValueType ([], [])
    | ETuple vs ->
      read_tuple_type env vs
    | ENonLinUnpack (vs, ts, v, e') ->
      (match find_type env v with
        | MultiValueType ([Tuple ts'], []) when ts = ts' -> 
          let env = add_variable_types env vs [] ts' [] in
          type_checker env e'
        | _ -> failwith("try to unpack the tuple : " ^ v ^ " with the wrong number or type of variables"))
    | ELinUnpack (vs, ts, v, e') ->
      (match find_type env v with
        | MultiValueType ([], [Tuple ts']) when ts = ts' -> 
          let env = add_variable_types env [] vs [] ts' in
          let env = remove_type env v in
          let env, mvt = type_checker env e' in
          (match (are_variables_used env.env_lt vs) with
          | [] -> env, mvt
          | v::_ -> failwith("unused variable : " ^ v))
        | _ -> failwith("try to unpack the tuple : " ^ v ^ " with the wrong number or type of variables"))
 
(* tests if an environnement is empty for linear variables *)
let is_empty (env : environnementTypes) : (var * value_type) list =
  Environnement.bindings env.env_lt

(* finds the type of the result of a function and verifies if all the linear variables are used *)
let type_checker_function (env_ft : environnementFunctionTypes) (nlvs : var list) (lvs : var list) (nlts : value_type list) (lts : value_type list) (e : expr) : multivalue_type =
  let env = { env_nlt = Environnement.empty; env_lt = Environnement.empty; env_ft = env_ft } in
  let env = add_variable_types env nlvs lvs nlts lts in
  let env, mvt = type_checker env e in
  match is_empty env with
    | [] -> mvt
    | (v, _)::_ -> failwith("unsued linear variable : " ^ v)

(* returns the type of the result of a program *)
let rec interpret_type (env_ft : environnementFunctionTypes) (p : prog) : multivalue_type =
  match p with
    | [] -> failwith"empty program"
    | [FunDec ("main", [], [], [], [], e)] ->
      let env, mvt = type_checker { env_nlt = Environnement.empty; env_lt = Environnement.empty; env_ft = env_ft } e in
      (match is_empty env with
        | [] -> mvt
        | (v, _)::_ -> failwith("unsued linear variable : " ^ v))
    | (FunDec (f, nlvs, nlts, lvs, lts, e))::q ->
      let mvt = type_checker_function env_ft nlvs lvs nlts lts e in
      let env_ft = Environnement.add f (nlts, lts, mvt) env_ft in
      interpret_type env_ft q