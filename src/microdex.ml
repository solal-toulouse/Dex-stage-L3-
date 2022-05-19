open Syntax
open Print

module Environnement = Map.Make(String)

let counter() =
  let i = ref 0 in
  function () ->
    incr i;
    (string_of_int !i) ^ "*"

let fresh_name = counter()

(* The result of a program is always a float *)
let rec interpret (e : expr) (env_var : float Environnement.t) (env_func : (string * expr) Environnement.t) =
  match e with
  | EVar var ->
      Environnement.find var env_var
  | ELiteralI i ->
      float_of_int i
  | ELiteralF f ->
      f
  | EBinOp (e1, OpPlus, e2) ->
      interpret e1 env_var env_func +. interpret e2 env_var env_func
  | EBinOp (e1, OpMinus, e2) ->
      interpret e1 env_var env_func -. interpret e2 env_var env_func
  | EBinOp (e1, OpTimes, e2) ->
      interpret e1 env_var env_func *. interpret e2 env_var env_func
  | EBinOp (e1, OpDiv, e2) ->
      interpret e1 env_var env_func /. interpret e2 env_var env_func
  | EDecVar (name, e2, suite) ->
      let x = interpret e2 env_var env_func in
      let new_env_var = Environnement.add name x env_var
      in interpret suite new_env_var env_func
  | EDecFunc (f, var, e2, suite) ->
      let new_env_func = Environnement.add f (var, e2) env_func in
      interpret suite env_var new_env_func
  | EFunc (f, e2) ->
      let (var, f) = Environnement.find f env_func in
      let x = interpret e2 env_var env_func in
      let tempo_env_var = Environnement.add var x env_var in
      interpret f tempo_env_var env_func
  | ELin (f, x, tan) -> 
      let (var, e) = Environnement.find f env_func in
      let h = fresh_name() in
      let new_env_var = Environnement.add h (interpret tan env_var env_func) (Environnement.add var (interpret x env_var env_func) env_var) in
      let linear = linearize e var x h new_env_var env_func in
      interpret linear new_env_var env_func

(* linearize(f) return an expression corresponding to the differential of f. *)
and linearize (e : expr) (var : string) (x : expr) (h : string) (env_var : float Environnement.t) (env_func : (string * expr) Environnement.t): expr =
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
        let tan = Environnement.find h env_var in
        let f' = fresh_name() in
        let new_env_func = Environnement.add f' (var, xf) env_func in
        let h' = ELiteralF(interpret (ELin(f', x, ELiteralF(tan))) env_var new_env_func) in
        ELin(f, xf, h')
    | ELin (_) ->
        ELiteralF 0.0


let process (data : string) =
  let lexbuf = Lexing.from_string data in
  try
    (* Run the parser on this input. *)
    let e : expr = Parser.main Lexer.token lexbuf in
    let v = interpret e Environnement.empty Environnement.empty in
    Printf.printf "%f\n\n%!" v;
    print_expr(e);
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
