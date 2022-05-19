open Syntax
open Print

module Environnement = Map.Make(String)

let counter() =
  let i = ref 0 in
  function () ->
    incr i;
    (string_of_int !i) ^ "*"

let fresh_name = counter()

(* Type result to allow us to have different types of returned values *)
type result = F of float | C of result * result

let rec sum (x : result) (y : result) = match x, y with
  | F x', F y' -> F (x' +. y')
  | C (x1, x2), C (x3, x4) -> C (sum x1 x3, sum x2 x4)
  | _ -> failwith "Type error"

let rec diff (x : result) (y : result) = match x, y with
  | F x', F y' -> F (x' -. y')
  | C (x1, x2), C (x3, x4) -> C (diff x1 x3, diff x2 x4)
  | _ -> failwith "Type error"

let rec mul (x : result) (y : result) = match x, y with
  | F x', F y' -> F (x' *. y')
  | C (x1, x2), C (x3, x4) -> C (mul x1 x3, mul x2 x4)
  | _ -> failwith "Type error"

let rec div (x : result) (y : result) = match x, y with
  | F x', F y' -> F (x' /. y')
  | C (x1, x2), C (x3, x4) -> C (div x1 x3, div x2 x4)
  | _ -> failwith "Type error"

let rec print_result (x : result) = match x with
  | F x' ->
    Printf.fprintf stderr "%f" x'
  | C (x1, x2) ->
    Printf.fprintf stderr "(";
    print_result x1;
    Printf.fprintf stderr ",";
    print_result x2;
    Printf.fprintf stderr ")"

let rec expr_of_result (x : result) = match x with
  | F x' ->
    ELiteralF x'
  | C (x1, x2) ->
    ECouple (expr_of_result x1, expr_of_result x2)    

(* The interpretation of a program is always a result *)
let rec interpret (e : expr) (env_var : result Environnement.t) (env_func : (string * expr) Environnement.t) : result =
  match e with
  | EVar var ->
      Environnement.find var env_var
  | ELiteralI i ->
      F (float_of_int i)
  | ELiteralF f ->
      F f
  | EBinOp (e1, OpPlus, e2) ->
      let f1 = interpret e1 env_var env_func
      and f2 = interpret e2 env_var env_func in
      sum f1 f2
  | EBinOp (e1, OpMinus, e2) ->
      let f1 = interpret e1 env_var env_func
      and f2 = interpret e2 env_var env_func in
      diff f1 f2
  | EBinOp (e1, OpTimes, e2) ->
      let f1 = interpret e1 env_var env_func
      and f2 = interpret e2 env_var env_func in
      mul f1 f2
  | EBinOp (e1, OpDiv, e2) ->
      let f1 = interpret e1 env_var env_func
      and f2 = interpret e2 env_var env_func in
      div f1 f2
  | EDecVar (name, e2, suite) ->
      let x = interpret e2 env_var env_func in
      let new_env_var = Environnement.add name x env_var in
      interpret suite new_env_var env_func
  | EDecFunc (f, var, e2, suite) ->
      let new_env_func = Environnement.add f (var, e2) env_func in
      interpret suite env_var new_env_func
  | EFunc (f, e2) ->
      let (var, e3) = Environnement.find f env_func in
      let x = interpret e2 env_var env_func in
      let new_env_var = Environnement.add var x env_var in
      interpret e3 new_env_var env_func
  | ELin (f, x, tan) -> 
      let (var, e) = Environnement.find f env_func in
      let h = fresh_name() in
      let e2 = interpret x env_var env_func in
      let e3 = interpret tan env_var env_func in
      let new_env_var = Environnement.add h e3 (Environnement.add var e2 env_var) in
      let linear = linearize e var x h new_env_var env_func in
      interpret linear new_env_var env_func
  | ECouple (e1, e2) -> 
      C (interpret e1 env_var env_func, interpret e2 env_var env_func)

(* linearize(f) return an expression corresponding to the differential of f in x evaluated in h. *)
and linearize (e : expr) (var : string) (x : expr) (h : string) (env_var : result Environnement.t) (env_func : (string * expr) Environnement.t): expr =
  match e with
    | EVar y when y = var -> EVar h
    | EVar y ->
        let y' = y ^ "'" in
        if (Environnement.mem y' env_var) then
          EVar y'
        else ELiteralI 0
    | ELiteralI _ -> ELiteralI 0
    | ELiteralF _ -> ELiteralF 0.0
    | EBinOp (e1, OpPlus, e2) ->
        EBinOp (linearize e1 var x h env_var env_func, OpPlus, linearize e2 var x h env_var env_func)
    | EBinOp (e1, OpMinus, e2) ->
        EBinOp (linearize e1 var x h env_var env_func, OpMinus, linearize e2 var x h env_var env_func)
    | EBinOp (e1, OpTimes, e2) ->
        let e1' = EBinOp(linearize e1 var x h env_var env_func, OpTimes, e2)
        and e2' = EBinOp(e1, OpTimes, linearize e2 var x h env_var env_func)
        in EBinOp (e1', OpPlus, e2')
    | EBinOp (e1, OpDiv, e2) ->
        let e1' = linearize e1 var x h env_var env_func
        and e2' = linearize e2 var x h env_var env_func in
        let num = EBinOp (EBinOp(e1', OpTimes, e2), OpMinus, EBinOp(e1, OpTimes, e2'))
        and denom = EBinOp (e2, OpTimes, e2) in
        EBinOp (num, OpDiv, denom)
    | EDecVar (name, e2, suite) ->
        let name' = name ^ "'" in
        let e2' = interpret (linearize e2 var x h env_var env_func) env_var env_func in
        let new_env_var = Environnement.add name' e2' env_var in
        linearize suite var x h new_env_var env_func
    | EDecFunc (_, _, _, suite) ->
        linearize suite var x h env_var env_func
    | EFunc (f, xf) ->
        let tan = expr_of_result (Environnement.find h env_var) in
        let f' = fresh_name() in
        let new_env_func = Environnement.add f' (var, xf) env_func in
        let h' = expr_of_result (interpret (ELin(f', x, tan)) env_var new_env_func) in
        ELin(f, xf, h')
    | ELin (_) ->
        ELiteralF 0.0
    | ECouple (e1, e2) ->
        ECouple (linearize e1 var x h env_var env_func, linearize e2 var x h env_var env_func)


let process (data : string) =
  let lexbuf = Lexing.from_string data in
  try
    (* Run the parser on this input. *)
    let e : expr = Parser.main Lexer.token lexbuf in
    let v = interpret e Environnement.empty Environnement.empty in
    print_result v;
    Printf.fprintf stderr "\n\n%!";
    print_expr e;
    Printf.fprintf stderr "\n\n"
  with
  | Lexer.Error msg ->
      Printf.fprintf stderr "%s%!" msg
  | Parser.Error ->
      Printf.fprintf stderr "At offset %d: syntax error.\n%!"
        (Lexing.lexeme_start lexbuf)

let usage =
  "Usage: microdex <filename>"

let filename =
  ref None

let speclist = [
]

let () =
  Arg.parse speclist (fun f -> filename := Some f) usage

let filename =
  !filename

let read_whole_file filename =
  let ch = open_in filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let () =
  match filename with
  | None ->
      Printf.fprintf stderr "%s\n" usage;
      exit 1
  | Some f ->
      process (read_whole_file f)
