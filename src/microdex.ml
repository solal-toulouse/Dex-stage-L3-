open Syntax
open Print
open Type_checker
open Interpreter
open Transposition
open Unzipping
open Renaming

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

let empty_env_type = { env_nlt = Environnement.empty; env_lt = Environnement.empty; env_ft = Environnement.empty }

let process (data : string) =
  let lexbuf = Lexing.from_string data in
  try
    (* Run the parser on this input. *)
    let p : prog = Parser.main Lexer.token lexbuf in
    let _, _, p' = rename_variables_prog Environnement.empty Environnement.empty p in
    let p1, p2 = unzip_prog p' in
    print_prog p1;
    Printf.fprintf stderr "\n\n";
    print_prog p2;
    let p1' = transpose_prog empty_env_type empty_env_type p1 in
    let p2' = transpose_prog empty_env_type empty_env_type p2 in
    let mvt = interpret_type Environnement.empty p' in
    let mv = interpret empty_environnement p' in
    Printf.fprintf stderr "\nresultat : ";
    print_multivalue mv;
    Printf.fprintf stderr "\ntype : ";
    print_multivalue_type mvt;
    Printf.fprintf stderr "\n\n%!";
    Printf.fprintf stderr "\n\ntransposition linéaire :\n%!";
    print_prog p1';
    Printf.fprintf stderr "\n\ntransposition non linéaire :\n";
    print_prog p2'
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
