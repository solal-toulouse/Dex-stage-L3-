type binop =
  | OpPlus | OpMinus | OpTimes | OpDiv

type expr =
| ELiteralI of int
| ELiteralF of float
| EBinOp of expr * binop * expr
| EDecVar of string * expr * expr
| EVar of string
| EDecFonc of string * string * expr * expr
| EFonc of string * expr