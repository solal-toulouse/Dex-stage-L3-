{

  open Parser_high_level

  exception Error of string

}

rule token = parse
| [' ' '\t' '\n']
    { token lexbuf }
| ['0'-'9']+ ('.' ['0' - '9']) ? as f
    { FLOAT (float_of_string f)}
| "let"
    { LET }
| "def"
    { DEF }
| "in"
    { IN }
| "sin"
    { SIN }
| "cos"
    { COS }
| "exp"
    { EXP }
| "0l"
    { ZERO }
| "dup"
    { DUP }
| "drop"
    { DROP }
| "real"
    { REAL }
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
| "+."
    { LINPLUS }
| "*."
    { LINTIMES }
| '('
    { LPAREN }
| ')'
    { RPAREN }
| '['
    { LHOOK }
| ']'
    { RHOOK }
| ','
    { COMMA }
| ';'
    { SEMICOLON }
| ':'
    { DOUBLEDOTS }
| ['A'-'Z' 'a'-'z' '0'-'9' '_'] + as s
    { STRING s }
| eof
    { EOF }
| _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }
