open Syntax
open Print
(* open Interpreter *)
open Transposition
open Unzipping
open Linearize
open Type_checker
open Pre_treatment
open Translate
(* open Generate_expression *)

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
    (* for _ = 0 to 100 do
      let p1 = generate_prog Environnement.empty 2 100 4 in *)
      let p1 : prog_hl = Parser_high_level.main Lexer.token lexbuf in
      Printf.fprintf stderr "(1)";
      let p2 = translate_prog Environnement.empty p1 in
      Printf.fprintf stderr "(2)";
      let p2 = simplify_prog p2 in
      Printf.fprintf stderr "(3)";
      let _ = interpret_type Environnement.empty p2 in
      Printf.fprintf stderr "(4)";
      let p3 = linearize_prog Environnement.empty Environnement.empty p2 in
      Printf.fprintf stderr "(5)";
      let _ = interpret_type Environnement.empty p3 in
      Printf.fprintf stderr "(6)";
      let p3 = simplify_prog p3 in
      Printf.fprintf stderr "(7)";
      let _ = interpret_type Environnement.empty p3 in
      Printf.fprintf stderr "(8)";
      let pa, pb = unzip_prog p3 in
      Printf.fprintf stderr "(9)";
      let _ = interpret_type Environnement.empty pa in
      let _ = interpret_type Environnement.empty pb in
      Printf.fprintf stderr "(10)";
      let pa' = simplify_prog2 pa in
      Printf.fprintf stderr "(12)";
      let _ = interpret_type Environnement.empty pa' in
      Printf.fprintf stderr "(13)";
      let pb' = transpose_prog empty_env_type empty_env_type pb in
      Printf.fprintf stderr "(14)";
      let _ = interpret_type Environnement.empty pb' in
      Printf.fprintf stderr "(15)";
      let pb' = simplify_prog pb' in
      Printf.fprintf stderr "(16)";
      let _ = interpret_type Environnement.empty pa' in
      Printf.fprintf stderr "(17)";
      let _ = interpret_type Environnement.empty pb' in
      Printf.fprintf stderr "(18)\n";
      print_prog pa';
      print_prog pb';
      let pb' = compress_prog pb' in
      print_prog_hl pb';
      (* Printf.fprintf stderr "\n\n";
      print_prog pa';
      Printf.fprintf stderr "\n\n";
      print_prog pb';
      print_multivalue_type mvta;
      Printf.fprintf stderr "\n\n";
      print_multivalue_type mvtb;
      Printf.fprintf stderr "\n\n"; *)
      (* done *)
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
