type binop =
  | OpPlus | OpMinus | OpTimes | OpDiv

type expr =
| ELiteralI of int
| ELiteralF of float
| EBinOp of expr * binop * expr
| EDecVar of string * expr * expr
| EVar of string
| EDecFunc of string * string * expr * expr
| EFunc of string * expr
| ELin of string * expr * expr