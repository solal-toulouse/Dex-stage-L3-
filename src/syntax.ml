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

type value = Real of float | Tuple of (value list)
type multivalue = MultiValue of value list * value list

type value_type = Real | Tuple of (value_type list)
type multivalue_type = MultiValueType of value_type list * value_type list

type expr =
| ENonLinLiteral of float
| EVar of var
| ENonLinBinOp of var * binop * var
| ENonLinUnOp of unop * var
| ELinAdd of var * var
| ELinMul of var * var
| ETuple of var list
| ELinZero of value_type
| EMultiValue of (var list) * (var list)
| ELet of (var list) * (value_type list) * (var list) * (value_type list) * expr * expr
| ENonLinUnpack of (var list) * (value_type list) * var * expr
| ELinUnpack of (var list) * (value_type list) * var * expr
| EFunCall of funvar * (var list) * (var list)
| Dup of var
| Drop of expr

type dec_func = 
  FunDec of funvar * (var list) * (value_type list) * (var list) * (value_type list) * expr

type prog = dec_func list

(* How to store informations *)

module Environnement = Map.Make(String)
type environnementVariables = value Environnement.t
type environnementFunctions = ((var list) * (var list) * expr) Environnement.t
type environnement = { env_nlv : environnementVariables; env_lv : environnementVariables; env_f : environnementFunctions }

type environnementVariableTypes = value_type Environnement.t
type environnementFunctionTypes = (value_type list * value_type list * multivalue_type) Environnement.t
type environnementTypes = { env_nlt : environnementVariableTypes; env_lt : environnementVariableTypes; env_ft : environnementFunctionTypes }

type environnementFunctionUnzipping = (funvar * value_type list * funvar * value_type list) Environnement.t

(* Syntax high level *)
type multivalue_hl = HLMultiValue of value list

type multivalue_type_hl = HLMultiValueType of value_type list

type expr_hl =
| HLLiteral of float
| HLVar of var
| HLBinOp of expr_hl * binop * expr_hl
| HLUnOp of unop * expr_hl
| HLTuple of expr_hl list
| HLMultiValue of (expr_hl list)
| HLLet of (var list) * (value_type list) * expr_hl * expr_hl
| HLUnpack of (var list) * (value_type list) * expr_hl * expr_hl
| HLFunCall of funvar * (expr_hl list)

type dec_func_hl = 
  HLFunDec of funvar * (var list) * (value_type list) * expr_hl

type prog_hl = dec_func_hl list