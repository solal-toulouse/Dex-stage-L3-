open Syntax

let rec print_string_list l = match l with
  | [] -> ()
  | [a] ->
    Printf.fprintf stderr "%s" a
  | t::q ->
    Printf.fprintf stderr "%s, " t;
    print_string_list q

let print_type (t : value_type) = 
  match t with
    | R -> Printf.fprintf stderr "real"
  
let rec print_var_list vs ts = match vs, ts with
  | [], [] -> ()
  | [v], [t] ->
    Printf.fprintf stderr "%s : " v;
    print_type t
  | v::q1, t::q2 ->
    Printf.fprintf stderr "%s : " v;
    print_type t;
    Printf.fprintf stderr ", ";
    print_var_list q1 q2
  | _ -> failwith"wrong type"

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
    print_string_list nlvs;
    Printf.fprintf stderr "; ";
    print_string_list lvs;
    Printf.fprintf stderr ")"
  | EDec (nlvs, nlts, lvs, lts, e_op, e_mn) ->
    Printf.fprintf stderr "let (";
    print_var_list nlvs nlts;
    Printf.fprintf stderr "; ";
    print_var_list lvs lts;
    Printf.fprintf stderr ") = ";
    print_expr e_op;
    Printf.fprintf stderr " in \n";
    print_expr e_mn
  | EFunCall (f, l1, l2) ->
    Printf.fprintf stderr "%s(" f;
    print_string_list l1;
    Printf.fprintf stderr "; ";
    print_string_list l2;
    Printf.fprintf stderr ")"
  | Dup v ->
    Printf.fprintf stderr "dup(%s)" v
  | Drop v ->
    Printf.fprintf stderr "drop(%s)" v

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
    print_var_list nlvs nlts;
    Printf.fprintf stderr "; ";
    print_var_list lvs lts;
    Printf.fprintf stderr ") = \n";
    print_expr e;
    Printf.fprintf stderr "\n\n";
    print_prog q