{

  open Parser

  exception Error of string

}

rule token = parse
| [' ' '\t' '\n']
    { token lexbuf }
| ['0'-'9']+ as i
    { INT (int_of_string i) }
| ['0'-'9']+ ('.' ['0' - '9']) ? as f
    { FLOAT (float_of_string f)}
| "let"
    { LET }
| "in"
    { IN }
| "linearize"
    { LINEARIZE }
| '='
    { EQUAL }
| '+'
    { PLUS }
| '-'
    { MINUS }
| '*'
    { TIMES }
| '/'
    { DIV }
| '('
    { LPAREN }
| ')'
    { RPAREN }
| ','
    { COMMA }
| ['A'-'Z' 'a'-'z' '0'-'9' '_'] + as s
    { STRING s }
| eof
    { EOF }
| _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }
