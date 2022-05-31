open Syntax

let rec print_multivalue (mv : multivalue) =
  let MultiValue (lvs, nlvs) = mv in
  Printf.fprintf stderr "(";
  print_value_list lvs;
  Printf.fprintf stderr "; ";
  print_value_list nlvs;
  Printf.fprintf stderr ")"

and print_value_list (l : value list) =
  match l with
    | [] -> ()
    | t::[] ->
      print_value t
    | t::q ->
      print_value t;
      Printf.fprintf stderr ",";
      print_value_list q

and print_value (v : value) =
  let R f = v in
  Printf.fprintf stderr "%f" f

let nlbinop (v1 : multivalue) (op : binop) (v2 : multivalue) : multivalue =
  match v1, v2 with
    | MultiValue ([R f1], []), MultiValue ([R f2], []) ->
      (match op with
        | OpPlus -> MultiValue ([R (f1 +. f2)], [])
        | OpMinus -> MultiValue ([R (f1 -. f2)], [])
        | OpTimes -> MultiValue ([R (f1 *. f2)], [])
        | OpDiv -> MultiValue ([R (f1 /. f2)], []))
    | _ -> failwith"binary operation between unauthorize types"

let unop (v : multivalue) (op : unop) : multivalue =
  match v with
    | MultiValue ([R f], []) ->
      (match op with
        | OpCos -> MultiValue([R (cos f)], [])
        | OpSin -> MultiValue([R (sin f)], [])
        | OpExp -> MultiValue([R (exp f)], []))
    | _ -> failwith"unary operation on an unauthorized type"

let linadd (v1 : multivalue) (v2 : multivalue) : multivalue =
  match v1, v2 with
    | MultiValue ([], [R f1]), MultiValue ([], [R f2]) ->
      MultiValue ([], [R (f1 +. f2)])
    | _ -> failwith"binary operation between non authorize types"

let linmul (v1 : multivalue) (v2 : multivalue) : multivalue =
  match v1, v2 with
    | MultiValue ([], [R f1]), MultiValue ([R f2], []) ->
      MultiValue ([], [R (f1 *. f2)])
    | MultiValue ([R f1], []), MultiValue ([], [R f2]) ->
    MultiValue ([], [R (f1 *. f2)])
    | _ -> failwith"binary operation between non authorize types"

(* How to stock variables and their value or functions *)

let empty_environnement () =
  { env_nlv = Environnement.empty; env_lv = Environnement.empty; env_f = Environnement.empty }

let print_env_var (env : environnement) =
  let env_nlv, env_lv = env.env_nlv, env.env_lv in
  let l1, l2 = Environnement.bindings env_nlv, Environnement.bindings env_lv in
  let rec aux l = match l with
    | [] -> ()
    | (k, x)::q ->
      Printf.fprintf stderr "%s," k;
      print_value x;
      Printf.fprintf stderr "\n";
      aux q
  in Printf.fprintf stderr "non linear : \n";
  aux l1;
  Printf.fprintf stderr "linear : \n";
  aux l2

let read_values (env : environnement) (nlvs : var list) (lvs : var list) : multivalue =
  let env_nlvs, env_lvs = env.env_nlv, env.env_lv in
  let rec aux (env_v : environnementVariables) (vs : var list) : value list =
    match vs with
      | [] -> []
      | a::b ->
        let x = Environnement.find a env_v in
        x :: (aux env_v b)
  in MultiValue (aux env_nlvs nlvs, aux env_lvs lvs)

let add_variables (env : environnement) (nlvs : var list) (lvs : var list) (nlxs : value list) (lxs : value list) : environnement =
  let env_nlv, env_lv, env_f = env.env_nlv, env.env_lv, env.env_f in
  let rec aux vs xs env_var =
    match vs, xs with
      | [], [] -> env_var
      | [], _| _, [] -> failwith"type error"
      | a::b, c::d ->
        let new_env_var = Environnement.add a c env_var in
        aux b d new_env_var
  in { env_nlv = aux nlvs nlxs env_nlv ; env_lv = aux lvs lxs env_lv; env_f = env_f}

let find (env : environnement) (v : var) : multivalue =
  try
    MultiValue ([Environnement.find v env.env_nlv], [])
  with
    Not_found -> MultiValue ([], [Environnement.find v env.env_lv])

let rec execute (env : environnement) (e : expr) : multivalue =
  match e with
    | EMultiValue (nlvs, lvs) -> read_values env nlvs lvs
    | EDec (nlvs, _, lvs, _, e1, e2) ->
      let MultiValue (nlxs, lxs) = execute env e1 in
      let new_env = add_variables env nlvs lvs nlxs lxs
      in execute new_env e2
    | EFunCall (f, nlv1s, lv1s) -> 
      let nlv2s, lv2s, e = Environnement.find f env.env_f in
      let MultiValue (nlxs, lxs) = read_values env nlv1s lv1s in
      let new_env = add_variables env nlv2s lv2s nlxs lxs in
      execute new_env e
    | ENonLinLiteral f -> MultiValue ([R f], [])
    | EVar v ->
      find env v
    | ENonLinBinOp (v1, op, v2) -> 
      let x1, x2 = find env v1, find env v2 in
      nlbinop x1 op x2
    | ENonLinUnOp (op, v) ->
      let x = find env v in
      unop x op
    | ELinAdd (v1, v2) ->
      let x1, x2 = find env v1, find env v2 in
      linadd x1 x2
    | ELinMul (v1, v2) ->
      let x1, x2 = find env v1, find env v2 in
      linmul x1 x2
    | ELinZero R -> MultiValue ([], [R 0.0])
    | Dup v -> 
      (match read_values env [] [v] with
        | MultiValue ([], [x]) ->
            MultiValue ([], [x; x])
        | _ -> failwith"type error")
    | Drop _ -> MultiValue ([], [])

let rec interpret (env : environnement) (p : prog) =
  match p with
    | [] -> failwith"empty program"
    | [FunDec ("main", [], [], [], [], e)] ->
      execute env e
    | (FunDec (f, nlvs, _, lvs, _, e))::q ->
      let new_env_f = Environnement.add f (nlvs, lvs, e) env.env_f
      in interpret {env_nlv = env.env_nlv; env_lv = env.env_lv; env_f = new_env_f } q
