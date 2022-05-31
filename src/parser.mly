%token <float> FLOAT
%token <string> STRING
%token LET IN DEF
%token ZERO
%token PLUS MINUS TIMES DIV EQUAL
%token LINPLUS LINTIMES
%token R
%token SIN COS EXP
%token DROP DUP
%token LPAREN RPAREN COMMA SEMICOLON DOUBLEDOTS
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
  | DEF; f = STRING; LPAREN; nlvs = separated_list(COMMA, STRING); DOUBLEDOTS; nlts = separated_list(COMMA, value_type); SEMICOLON; lvs = separated_list(COMMA, STRING); DOUBLEDOTS; lts = separated_list(COMMA, value_type); RPAREN; EQUAL; e = expr;
    { FunDec (f, nlvs, nlts, lvs, lts, e) }
  | DEF; f = STRING; LPAREN; nlvs = separated_list(COMMA, STRING); DOUBLEDOTS; nlts = separated_list(COMMA, value_type); SEMICOLON; RPAREN; EQUAL; e = expr;
    { FunDec (f, nlvs, nlts, [], [], e) }
  | DEF; f = STRING; LPAREN; SEMICOLON; lvs = separated_list(COMMA, STRING); DOUBLEDOTS; lts = separated_list(COMMA, value_type); RPAREN; EQUAL; e = expr;
    { FunDec (f, [], [], lvs, lts, e) }
  | DEF; f = STRING; LPAREN; SEMICOLON; RPAREN; EQUAL; e = expr;
    { FunDec (f, [], [], [], [], e) }

let expr :=
  | LPAREN; nlvs = separated_list(COMMA, STRING); SEMICOLON; lvs = separated_list(COMMA, STRING); RPAREN;
    { EMultiValue (nlvs, lvs) }
  | LET; LPAREN; nlvs = separated_list(COMMA, STRING); DOUBLEDOTS; nlts = separated_list(COMMA, value_type); SEMICOLON; lvs = separated_list(COMMA, STRING); DOUBLEDOTS; lts = separated_list(COMMA, value_type); RPAREN; EQUAL; e1 = expr; IN; e2 = expr;
    { EDec (nlvs, nlts, lvs, lts, e1, e2) }
  | LET; LPAREN; nlvs = separated_list(COMMA, STRING); DOUBLEDOTS; nlts = separated_list(COMMA, value_type); SEMICOLON; RPAREN; EQUAL; e1 = expr; IN; e2 = expr;
    { EDec (nlvs, nlts, [], [], e1, e2) }
  | LET; LPAREN; SEMICOLON; lvs = separated_list(COMMA, STRING); DOUBLEDOTS; lts = separated_list(COMMA, value_type); RPAREN; EQUAL; e1 = expr; IN; e2 = expr;
    { EDec ([], [], lvs, lts, e1, e2) }
  | LET; LPAREN; SEMICOLON; RPAREN; EQUAL; e1 = expr; IN; e2 = expr;
    { EDec ([], [], [], [], e1, e2) }
  /* | LET; LPAREN; l = separated_list(COMMA, STRING); SEMICOLON; RPAREN; EQUAL; t = tuple; IN; e_mn = expr;
    { EUnpack (l, t, e_mn) } */
  /* | LET; LPAREN; SEMICOLON; l = separated_list(COMMA, STRING); RPAREN; EQUAL; t = tuple; IN; e_mn = expr;
    { EUnpack (l, t, e_mn) } */
  | f = STRING; LPAREN; nlvs = separated_list(COMMA, STRING); SEMICOLON; lvs = separated_list(COMMA, STRING); RPAREN;
    { EFunCall (f, nlvs, lvs) }
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
  | LPAREN; ZERO; DOUBLEDOTS; t = value_type; RPAREN;
    { ELinZero t }
  | DUP; LPAREN; v = STRING; RPAREN;
    { Dup v }
  | DROP; LPAREN; v = STRING; RPAREN;
    { Drop v }

/* let tuple :=
  LPAREN; l = separated_list(COMMA, STRING); RPAREN;
    { ETuple l } */

let value_type ==
  | R;
    { R }

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

