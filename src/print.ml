open Syntax

let rec print_string_list l = match l with
  | [] -> ()
  | [a] ->
    Printf.fprintf stderr "%s" a
  | t::q ->
    Printf.fprintf stderr "%s," t;
    print_string_list q

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
  | ELinZero ->
    Printf.fprintf stderr "0"
  | EMultiValue (l1, l2) ->
    Printf.fprintf stderr "(";
    print_string_list l1;
    Printf.fprintf stderr ";";
    print_string_list l2;
    Printf.fprintf stderr ")"
  | EDec (l1, l2, e_op, e_mn) ->
    Printf.fprintf stderr "let (";
    print_string_list l1;
    Printf.fprintf stderr ";";
    print_string_list l2;
    Printf.fprintf stderr ") = ";
    print_expr e_op;
    Printf.fprintf stderr " in \n";
    print_expr e_mn
  | EFunCall (f, l1, l2) ->
    Printf.fprintf stderr "%s(" f;
    print_string_list l1;
    Printf.fprintf stderr ";";
    print_string_list l2;
    Printf.fprintf stderr ")"

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
  | FunDec (f, nlvar, lvar, e)::q ->
    Printf.fprintf stderr "def %s(" f;
    print_string_list nlvar;
    Printf.fprintf stderr ";";
    print_string_list lvar;
    Printf.fprintf stderr ") = \n";
    print_expr e;
    Printf.fprintf stderr "\n\n";
    print_prog q