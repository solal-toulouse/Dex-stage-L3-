open Syntax
open Print

module Variable = 
  struct
    type t = string
    let compare x y =
      Stdlib.compare x y
    end

module Environnement = Map.Make(Variable)

let rec interpret (e : expr) (env : float Environnement.t) =
  match e with
  | EVar var ->
      Environnement.find var env
  | ELiteralI i ->
      float_of_int i
  | ELiteralF f ->
      f
  | EBinOp (e1, OpPlus, e2) ->
      interpret e1 env +. interpret e2 env
  | EBinOp (e1, OpMinus, e2) ->
      interpret e1 env -. interpret e2 env
  | EBinOp (e1, OpTimes, e2) ->
      interpret e1 env *. interpret e2 env
  | EBinOp (e1, OpDiv, e2) ->
      interpret e1 env /. interpret e2 env
  | EDecVar (name, e1, e2) ->
      let x = interpret e1 env in
      let new_env = Environnement.add name x env
      in interpret e2 new_env

let process (data : string) =
  let lexbuf = Lexing.from_string data in
  try
    (* Run the parser on this input. *)
    let e : expr = Parser.main Lexer.token lexbuf in
    print_expr(e);
    Printf.fprintf stderr "\n";
    let v = interpret e Environnement.empty in
    Printf.printf "%f\n%!" v
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
