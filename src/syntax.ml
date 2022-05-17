type binop =
  | OpPlus | OpMinus | OpTimes | OpDiv

type expr =
| ELiteral of int
| EBinOp of expr * binop * expr
