type binop =
| OpPlus
| OpMinus
| OpTimes
| OpDiv

type unop =
| OpSin
| OpCos
| OpExp

type var = string
type funvar = string

type expr =
| ENonLinLiteral of float
| EVar of var
| ENonLinBinOp of var * binop * var
| ENonLinUnOp of unop * var
| ELinAdd of var * var
| ELinMul of var * var
(* | ETuple of string list *)
| ELinZero
| EMultiValue of (var list) * (var list)
| EDec of (var list) * (var list) * expr * expr
(* | EUnpack of (string list)  * expr * expr *)
| EFunCall of funvar * (var list) * (var list)

type dec_func = 
  FunDec of funvar * var list * var list * expr

type prog = dec_func list