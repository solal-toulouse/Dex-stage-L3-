%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token LET IN
%token PLUS MINUS TIMES DIV EQUAL
%token LPAREN RPAREN COMMA
%token LINEARIZE
%token EOF
%start <Syntax.expr> main
%{ open Syntax %}

%%

(* -------------------------------------------------------------------------- *)

(* We wish to parse an expression followed with an end-of-line. *)

let main :=
  e = expr; EOF; { e }

(* An expression is an additive expression, a function declaration or a variable declaration. *)

let expr :=
  | e = additive_expr;
      { e }
  | v = variable_declaration;
      { v }
  | f = function_declaration;
      { f }

(* An additive expression is

   either a multiplicative expression,
   or the application of an additive operator to two subexpressions.

   In the second case, the left-hand subexpression is additive, while the
   right-hand subexpression is multiplicative; this reflects the fact that
   the operator is left-associative. The three semantic values of interest
   (the left subexpression, the operator, the right subexpression) are
   matched against ~ patterns, which means that, in the end, the data
   constructor [EBinOp] is applied to a tuple of these three components.
   Furthermore, this whole construction is wrapped in [located], so the
   result of [EBinOp], a raw expression, is turned into an expression. *)

let additive_expr :=
  | e = multiplicative_expr;
      { e }
  | e1 = additive_expr; op = additive_op; e2 = multiplicative_expr;
      { EBinOp (e1, op, e2) }

(* These are variables and functions declarations. *)

let variable_declaration :=
  LET; name = STRING; EQUAL; e = expr; IN; suite = expr;
      { EDecVar (name, e, suite) }
    
let function_declaration :=
  LET; f = STRING; var = STRING; EQUAL; e = expr; IN; suite = expr;
      { EDecFunc (f, var, e, suite) }

(* These are the additive operators and their meaning. *)

let additive_op ==
  | PLUS;  { OpPlus }
  | MINUS; { OpMinus }

(* A multiplicative expression is either an atomic expression or the
   application of a multiplicative operator to two subexpressions. *)

let multiplicative_expr :=
  | e = atomic_expr;
      { e }
  | e1 = multiplicative_expr; op = multiplicative_op; e2 = atomic_expr;
      { EBinOp(e1, op, e2) }

(* These are the multiplicative operators and their meaning. *)

let multiplicative_op ==
  | TIMES; { OpTimes }
  | DIV;   { OpDiv }

(* An atomic expression is one of:
   an expression between parentheses,
   a float or an integer literal,
   a variable or a function call. *)

let atomic_expr :=
  | LPAREN; e = additive_expr; RPAREN;
      { e }
  | i = INT;
      { ELiteralI i }
  | f = FLOAT;
      { ELiteralF f }
  | f = STRING; e = expr;
      { EFunc(f, e) }
  | LPAREN; LINEARIZE; f = STRING; x = expr; RPAREN; tan = expr;
      { ELin(f, x, tan) }
  | var = STRING;
      { EVar var }
  | LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN;
      { ECouple (e1, e2) }