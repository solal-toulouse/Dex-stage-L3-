%token <float> FLOAT
%token <string> STRING
%token LET IN DEF
%token ZERO
%token PLUS MINUS TIMES DIV EQUAL
%token LINPLUS LINTIMES
%token SIN COS EXP
%token LPAREN RPAREN COMMA SEMICOLON
%token EOF
%start <Syntax.prog> main
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
  DEF; f = STRING; LPAREN; nlvar = separated_list(COMMA, STRING); SEMICOLON; lvar = separated_list(COMMA, STRING); RPAREN; EQUAL; e = expr;
    { FunDec (f, nlvar, lvar, e) }

let expr :=
  | LPAREN; nlvar = separated_list(COMMA, STRING); SEMICOLON; lvar = separated_list(COMMA, STRING); RPAREN;
    { EMultiValue (nlvar, lvar) }
  | LET; LPAREN; nlvar = separated_list(COMMA, STRING); SEMICOLON; lvar = separated_list(COMMA, STRING); RPAREN; EQUAL; e_op = expr; IN; e_mn = expr;
    { EDec (nlvar, lvar, e_op, e_mn) }
  /* | LET; LPAREN; l = separated_list(COMMA, STRING); SEMICOLON; RPAREN; EQUAL; t = tuple; IN; e_mn = expr;
    { EUnpack (l, t, e_mn) } */
  /* | LET; LPAREN; SEMICOLON; l = separated_list(COMMA, STRING); RPAREN; EQUAL; t = tuple; IN; e_mn = expr;
    { EUnpack (l, t, e_mn) } */
  | f = STRING; LPAREN; l1 = separated_list(COMMA, STRING); SEMICOLON; l2 = separated_list(COMMA, STRING); RPAREN;
    { EFunCall (f, l1, l2) }
  | v1 = STRING; LINPLUS; v2 = STRING;
    { ELinAdd (v1, v2) }
  | v1 = STRING; LINTIMES; v2 = STRING;
    { ELinMul (v1, v2) }
  | LPAREN; e = expr; RPAREN;
    { e }
  | v = STRING;
    { EVar v }
  | lit = FLOAT;
    { ENonLinLiteral lit }
  /* | t = tuple;
    { t } */
  | op = unop; LPAREN; v = STRING; RPAREN;
    { ENonLinUnOp (op, v) }
  | v1 = STRING; op = binop; v2 = STRING;
    { ENonLinBinOp (v1, op, v2) }
  | ZERO;
    { ELinZero }

/* let tuple :=
  LPAREN; l = separated_list(COMMA, STRING); RPAREN;
    { ETuple l } */

let unop ==
  | SIN;
    { OpSin }
  | COS;
    { OpCos }
  | EXP;
    { OpExp }

let binop ==
  | PLUS;
    { OpPlus }
  | MINUS;
    { OpMinus }
  | TIMES;
    { OpTimes }
  | DIV;
    { OpDiv }

