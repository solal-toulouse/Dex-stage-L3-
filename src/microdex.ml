open Syntax

let rec interpret (e : expr) =
  match e with
  | ELiteral i ->
      i
  | EBinOp (e1, OpPlus, e2) ->
      interpret e1 + interpret e2
  | EBinOp (e1, OpMinus, e2) ->
      interpret e1 - interpret e2
  | EBinOp (e1, OpTimes, e2) ->
      interpret e1 * interpret e2
  | EBinOp (e1, OpDiv, e2) ->
      interpret e1 / interpret e2

let process (data : string) =
  let lexbuf = Lexing.from_string data in
  try
    (* Run the parser on this input. *)
    let e : expr = Parser.main Lexer.token lexbuf in
    let v = interpret e in
    Printf.printf "%d\n%!" v
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
