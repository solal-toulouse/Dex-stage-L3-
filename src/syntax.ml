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

type value = R of float
type multivalue = MultiValue of value list * value list

type value_type = R
type multivalue_type = MultiValueType of value_type list * value_type list

type expr =
| ENonLinLiteral of float
| EVar of var
| ENonLinBinOp of var * binop * var
| ENonLinUnOp of unop * var
| ELinAdd of var * var
| ELinMul of var * var
(* | ETuple of string list *)
| ELinZero of value_type
| EMultiValue of (var list) * (var list)
| EDec of (var list) * (value_type list) * (var list) * (value_type list) * expr * expr
(* | EUnpack of (string list)  * expr * expr *)
| EFunCall of funvar * (var list) * (var list)
| Dup of var
| Drop of var

type dec_func = 
  FunDec of funvar * (var list) * (value_type list) * (var list) * (value_type list) * expr

type prog = dec_func list

module Environnement = Map.Make(String)
type environnementVariables = value Environnement.t
type environnementFunctions = ((var list) * (var list) * expr) Environnement.t
type environnement = { env_nlv : environnementVariables; env_lv : environnementVariables; env_f : environnementFunctions}

type environnementVariableTypes = value_type Environnement.t
type environnementFunctionTypes = (value_type list * value_type list * multivalue_type) Environnement.t
type environnementTypes = { env_nlt : environnementVariableTypes; env_lt : environnementVariableTypes; env_ft : environnementFunctionTypes}
