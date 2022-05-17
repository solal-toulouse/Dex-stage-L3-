%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token EVar
%token LET IN
%token PLUS MINUS TIMES DIV EQUAL
%token LPAREN RPAREN
%token EOF

%start <Syntax.expr> main
%{ open Syntax %}

%%

(* -------------------------------------------------------------------------- *)

(* We wish to parse an expression followed with an end-of-line. *)

let main :=
  e = expr; EOF; { e }

(* An expression is an additive expression or a variable declaration. *)

let expr :=
  | e = additive_expr;
      { e }
  | v = variable_declaration;
      { v }

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

(* These are the additive operators and their meaning. *)

let variable_declaration :=
  LET; name = STRING; EQUAL; e1 = expr; IN; e2 = expr;
      { EDecVar (name, e1, e2) }

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
   an integer literal,
   an application of a unary operator to an atomic expression. *)

(* Only the last two cases are wrapped in [located]; in the first case, this is
   not necessary, as the expression already carries a location. Note that, this
   way, we get tight locations (i.e., the parentheses are not included). *)

let atomic_expr :=
  | LPAREN; e = additive_expr; RPAREN;
      { e }
  | i = INT;
      { ELiteralI i }
  | f = FLOAT;
      { ELiteralF f }
  | var = STRING;
      { EVar var }
