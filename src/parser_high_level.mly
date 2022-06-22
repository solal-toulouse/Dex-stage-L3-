%token <float> FLOAT
%token <string> STRING
%token LET IN DEF
%token ZERO
%token PLUS MINUS TIMES DIV EQUAL
%token LINPLUS LINTIMES
%token REAL
%token SIN COS EXP
%token DROP DUP
%token COMMA SEMICOLON DOUBLEDOTS
%token LPAREN RPAREN LHOOK RHOOK
%token EOF
%start <Syntax.prog_hl> main
%{ open Syntax %}

%%

(* -------------------------------------------------------------------------- *)

(* We wish to parse an list of declarations of functions followed with an end-of-line. *)

let main :=
  p = prog; EOF;
    { p }

let prog :=
  l = separated_list(SEMICOLON, function_declaration);
    { l }

let function_declaration :=
  | DEF; f = STRING; LPAREN; vs = separated_list(COMMA, STRING); DOUBLEDOTS; ts = separated_list(COMMA, value_type); RPAREN; EQUAL; e = expr_hl;
    { HLFunDec (f, vs, ts, e) }
  | DEF; f = STRING; LPAREN; RPAREN; EQUAL; e = expr_hl;
    { HLFunDec (f, [], [], e) }


let expr_hl :=
  | e = additive_expr;
      { e }
  | LET; LPAREN; vs = separated_list(COMMA, STRING); DOUBLEDOTS; ts = separated_list(COMMA, value_type); RPAREN; EQUAL; e1 = expr_hl; IN; e2 = expr_hl;
    { HLLet (vs, ts, e1, e2) }
  | LET; LPAREN; LHOOK; vs = separated_list(COMMA, STRING); RHOOK; DOUBLEDOTS; LHOOK; ts = separated_list(COMMA, value_type); RHOOK; RPAREN; EQUAL; e1 = expr_hl; IN; e2 = expr_hl;
    { HLUnpack (vs, ts, e1, e2) }

 let additive_expr :=
   | e = multiplicative_expr;
       { e }
   | e1 = additive_expr; op = additive_op; e2 = multiplicative_expr;
       { HLBinOp (e1, op, e2) }

 let additive_op ==
   | PLUS;  { OpPlus }
   | MINUS; { OpMinus }

 let multiplicative_expr :=
   | e = atomic_expr;
       { e }
   | e1 = multiplicative_expr; op = multiplicative_op; e2 = atomic_expr;
       { HLBinOp(e1, op, e2) }

 let multiplicative_op ==
   | TIMES; { OpTimes }
   | DIV;   { OpDiv }

 let atomic_expr :=
  | f = STRING; LPAREN; es = separated_list(COMMA, expr_hl); RPAREN;
    { HLFunCall (f, es) }
  | LPAREN; e = expr_hl; RPAREN;
    { e }
  | v = STRING;
    { HLVar v }
  | lit = FLOAT;
    { HLLiteral lit }
  | LHOOK; es = separated_list(COMMA, expr_hl); RHOOK;
    { HLTuple es }
  | op = unop; LPAREN; e = expr_hl; RPAREN;
    { HLUnOp (op, e) }
  | LPAREN; e = expr_hl; COMMA; es = separated_nonempty_list(COMMA, expr_hl); RPAREN;
    { HLMultiValue (e::es) }

let value_type ==
  | REAL;
    { Real }
  | LHOOK; ts = separated_list(COMMA, value_type); RHOOK;
    { Tuple ts }

let unop ==
  | SIN;
    { OpSin }
  | COS;
    { OpCos }
  | EXP;
    { OpExp }