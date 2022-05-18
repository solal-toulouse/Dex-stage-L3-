open Syntax

let rec print_expr(e) = match e with
  | EDecVar(name, e1, e2) ->
    Printf.fprintf stderr "let ";
    Printf.fprintf stderr "%s" name;
    Printf.fprintf stderr " = ";
    print_additive_expr(e1);
    Printf.fprintf stderr " in ";
    print_expr(e2)
  | EDecFonc(name, var, e1, e2) ->
    Printf.fprintf stderr "let ";
    Printf.fprintf stderr "%s" name;
    Printf.fprintf stderr "(";
    Printf.fprintf stderr "%s" var;
    Printf.fprintf stderr ")";
    Printf.fprintf stderr " = ";
    print_additive_expr(e1);
    Printf.fprintf stderr " in ";
    print_expr(e2)
  | e -> print_additive_expr(e)

and print_op(op) = match op with
  | OpTimes -> Printf.fprintf stderr "*"
  | OpDiv -> Printf.fprintf stderr "/"
  | OpPlus -> Printf.fprintf stderr "+"
  | OpMinus -> Printf.fprintf stderr "-"

and print_multiplicative_expr(e) = match e with
  | EBinOp(e1, op, e2) ->
    Printf.fprintf stderr ")";
    print_multiplicative_expr(e1);
    print_op(op);
    print_atomic_expr(e2);
    Printf.fprintf stderr ")"
  | e ->
    print_atomic_expr(e);

and print_additive_expr (e) = match e with
  | EBinOp(e1, op, e2) ->
    Printf.fprintf stderr "(";
    print_additive_expr(e1);
    print_op(op);
    print_multiplicative_expr(e2);
    Printf.fprintf stderr ")"
  | e -> 
    print_multiplicative_expr(e);

and print_atomic_expr(e) = match e with
  | ELiteralI i -> Printf.fprintf stderr "%d" i;
  | ELiteralF f -> Printf.fprintf stderr "%f" f;
  | EVar var -> Printf.fprintf stderr "%s" var;
  | EFonc(name, e) ->
    Printf.fprintf stderr "%s" name;
    Printf.fprintf stderr "(";
    print_expr(e);
    Printf.fprintf stderr ")"
  | e -> 
    print_additive_expr(e);