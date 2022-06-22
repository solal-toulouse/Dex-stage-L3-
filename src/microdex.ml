open Syntax
open Print
(* open Interpreter *)
(* open Type_checker
open Transposition
open Unzipping *)
open Pre_treatment
(* open Linearize *)
open Translate

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

let empty_env_type = { env_nlt = Environnement.empty; env_lt = Environnement.empty; env_ft = Environnement.empty }
let empty_env = { env_nlv = Environnement.empty; env_lv = Environnement.empty; env_f = Environnement.empty }

let process (data : string) =
  let lexbuf = Lexing.from_string data in
  try
    (* Run the parser on this input. *)
    let p : prog_hl = Parser_high_level.main Lexer.token lexbuf in
    let p' = translate_prog Environnement.empty p in
    let p' = simplify_prog p' in
    print_prog p'
    (* let _ = interpret_type Environnement.empty p in
    let p' = linearize_prog Environnement.empty Environnement.empty p in
    let p' = simplify_prog p' in
    let p1, p2 = unzip_prog p' in
    print_prog p1;
    print_prog p2;
    let p1' = transpose_prog empty_env_type empty_env_type p1 in
    let p1' = simplify_prog p1' in
    let p2' = transpose_prog empty_env_type empty_env_type p2 in
    let p2' = simplify_prog p2' in
    let mvt1 = interpret_type Environnement.empty p1' in
    let mvt2 = interpret_type Environnement.empty p2' in
    Printf.fprintf stderr "\n\n";
    print_prog p1';
    Printf.fprintf stderr "\n\n";
    print_prog p2';
    print_multivalue_type mvt1;
    Printf.fprintf stderr "\n\n";
    print_multivalue_type mvt2;
    Printf.fprintf stderr "\n\n"; *)
  with
  | Lexer.Error msg ->
      Printf.fprintf stderr "%s%!" msg
  | Parser_high_level.Error ->
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
