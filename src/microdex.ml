open Syntax
open Print
open Type_checker
open Interpreter

(* names :
value : x, y, z
multivalue : mv, mv1, mv2
variables : v, v1, v2
environnements : env, env_nlv, env_lv
expressions : e, e1, e2 
type : t, t1, t2
multivalue type : mvt, mvt1, mvt2
listes : ~s
lineaires : l~
non_linéaire : nl~ *)

(* TODO :
    - ajouter les tuples
    - ajouter la localisation des erreurs de parsage *)

let process (data : string) =
  let lexbuf = Lexing.from_string data in
  try
    (* Run the parser on this input. *)
    let p : prog = Parser.main Lexer.token lexbuf in
    let mvt = interpret_type Environnement.empty p in
    let v = interpret (empty_environnement ()) p in
    Printf.fprintf stderr "\nresultat : ";
    print_multivalue v;
    Printf.fprintf stderr "\ntype : ";
    print_multivalue_type mvt;
    Printf.fprintf stderr "\n\n%!";
    print_prog p
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
