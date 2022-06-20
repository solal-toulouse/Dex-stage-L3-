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

and print_value (x : value) =
  match x with
    | Real f ->
      Printf.fprintf stderr "%f" f
    | Tuple xs ->
      Printf.fprintf stderr "[";
      print_value_list xs;
      Printf.fprintf stderr "]"

let print_env (env : environnement) =
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

let print_env_var (env : 'a Environnement.t) =
  let l = Environnement.bindings env in
  let rec aux l = match l with
    | [] -> ()
    | (a, b)::q ->
        Printf.fprintf stderr "(%s, %s)" a b;
        aux q
  in aux l

let rec print_var_list l = match l with
  | [] -> ()
  | [a] ->
    Printf.fprintf stderr "%s" a
  | t::q ->
    Printf.fprintf stderr "%s, " t;
    print_var_list q

let rec print_type (t : value_type) = 
  match t with
    | Real -> Printf.fprintf stderr "real"
    | Tuple ts ->
      Printf.fprintf stderr "[";
      print_type_list ts;
      Printf.fprintf stderr "]"

and print_type_list (ts : value_type list) =
  match ts with
    | [] -> ()
    | [t] -> print_type t
    | t::q ->
      print_type t;
      Printf.fprintf stderr ", ";
      print_type_list q

let rec print_var_type_list vs ts =
  match vs, ts with
    | [], [] -> ()
    | [v], [t] ->
      Printf.fprintf stderr "%s : " v;
      print_type t
    | v::q1, t::q2 ->
      Printf.fprintf stderr "%s : " v;
      print_type t;
      Printf.fprintf stderr ", ";
      print_var_type_list q1 q2
    | _ -> failwith"wrong type"

let print_multivalue_type (mvt : multivalue_type) =
  let MultiValueType (lvs, nlvs) = mvt in
  Printf.fprintf stderr "(";
  print_type_list lvs;
  Printf.fprintf stderr "; ";
  print_type_list nlvs;
  Printf.fprintf stderr ")"

let print_env_type (env : environnementTypes) =
  let env_nlt, env_lt = env.env_nlt, env.env_lt in
  let l1, l2 = Environnement.bindings env_nlt, Environnement.bindings env_lt in
  let rec aux l = match l with
    | [] -> ()
    | (k, t)::q ->
      Printf.fprintf stderr "%s : " k;
      print_type t;
      Printf.fprintf stderr "\n";
      aux q
  in Printf.fprintf stderr "non linear : \n";
  aux l1;
  Printf.fprintf stderr "linear : \n";
  aux l2

let rec print_expr (e : expr) = match e with
  | ENonLinLiteral f ->
    Printf.fprintf stderr "%f" f
  | EVar v ->
    Printf.fprintf stderr "%s" v
  | ENonLinBinOp (v1, op, v2) ->
    Printf.fprintf stderr "%s " v1;
    print_binop op;
    Printf.fprintf stderr " %s" v2
  | ENonLinUnOp (op, v) ->
    print_unop op;
    Printf.fprintf stderr "(%s)" v;
  | ELinAdd (v1, v2) ->
    Printf.fprintf stderr "%s +. %s" v1 v2
  | ELinMul (v1, v2) ->
    Printf.fprintf stderr "%s *. %s" v1 v2
  | ELinZero t ->
    Printf.fprintf stderr "(0 : ";
    print_type t;
    Printf.fprintf stderr ")"
  | EMultiValue (nlvs, lvs) ->
    Printf.fprintf stderr "(";
    print_var_list nlvs;
    Printf.fprintf stderr "; ";
    print_var_list lvs;
    Printf.fprintf stderr ")"
  | EDec (nlvs, nlts, lvs, lts, e_op, e_mn) ->
    Printf.fprintf stderr "let (";
    print_var_type_list nlvs nlts;
    Printf.fprintf stderr "; ";
    print_var_type_list lvs lts;
    Printf.fprintf stderr ") = \n";
    print_expr e_op;
    Printf.fprintf stderr " in \n";
    print_expr e_mn
  | EFunCall (f, l1, l2) ->
    Printf.fprintf stderr "%s(" f;
    print_var_list l1;
    Printf.fprintf stderr "; ";
    print_var_list l2;
    Printf.fprintf stderr ")"
  | Dup v ->
    Printf.fprintf stderr "dup(%s)" v
  | Drop e ->
    Printf.fprintf stderr "drop(";
    print_expr e;
    Printf.fprintf stderr ")"
  | ETuple vs ->
    Printf.fprintf stderr "[";
    print_var_list vs;
    Printf.fprintf stderr "]"
  | ENonLinUnpack (vs, ts, v, e) ->
    Printf.fprintf stderr "let ([";
    print_var_list vs;
    Printf.fprintf stderr "] : [";
    print_type_list ts;
    Printf.fprintf stderr "];) = %s in \n" v;
    print_expr e
  | ELinUnpack (vs, ts, v, e) ->
    Printf.fprintf stderr "let (;[";
    print_var_list vs;
    Printf.fprintf stderr "] : [";
    print_type_list ts;
    Printf.fprintf stderr "]) = %s in \n" v;
    print_expr e

and print_binop(op) = match op with
  | OpTimes -> Printf.fprintf stderr "*"
  | OpDiv -> Printf.fprintf stderr "/"
  | OpPlus -> Printf.fprintf stderr "+"
  | OpMinus -> Printf.fprintf stderr "-"

and print_unop(op) = match op with
  | OpCos -> Printf.fprintf stderr "cos"
  | OpSin -> Printf.fprintf stderr "sin"
  | OpExp -> Printf.fprintf stderr "exp"

and print_prog (p : prog) = match p with
  | [] -> ()
  | FunDec (f, nlvs, nlts, lvs, lts, e)::q ->
    Printf.fprintf stderr "def %s(" f;
    print_var_type_list nlvs nlts;
    Printf.fprintf stderr "; ";
    print_var_type_list lvs lts;
    Printf.fprintf stderr ") = \n";
    print_expr e;
    Printf.fprintf stderr "\n\n";
    print_prog q