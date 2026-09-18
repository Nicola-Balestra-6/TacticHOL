{
  open Tactic_parser
  (* Bring Menhir token constructors (THEN, LPAREN, RAW, EOF, ...) into scope. *)

  let keyword = function
    | "THENL"  -> THENL
    | "THEN"   -> THEN
    | "ORELSE" -> ORELSE
    | "TRY"    -> TRY
    | "REPEAT" -> REPEAT
    | "let"    -> LET
    | "in"     -> IN
    | s        -> RAW s
}

(* One or more whitespace characters. These are skipped by the lexer. *)
let white = [' ' '\t' '\r' '\n']+

(* Identifiers used in tactic expressions.
   The apostrophe is included because HOL Light identifiers may end with '. *)
let ident = ['A'-'Z' 'a'-'z' '0'-'9' '_' '\'' ]+

(* Operator-like characters, returned as RAW chunks. *)
let op = ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~']+

(* Any character except NUL. Used as a fallback. *)
let any = [^ '\000']

(* Main lexer rule: converts the input lexbuf into Menhir tokens. *)
rule token = parse
  (* Skip whitespace. *)
  | white
      { token lexbuf }

  (* Identifiers are turned into keywords when recognized,
     otherwise they are emitted as RAW text. *)
  | ident as s
      { keyword s }

  (* Structural punctuation used by the parser. *)
  | '(' { LPAREN }
  | ')' { RPAREN }
  | ';' { SEMI }
  | '[' { LBRACK }
  | ']' { RBRACK }
  | '{' { LBRACE }
  | '}' { RBRACE }

  (* Quoted fragments are retained as is:
     their contents are not tokenized further and are returned as a single RAW token.
     This covers HOL Light terms and string-like fragments. *)
  | '`'
      { RAW ("`" ^ lex_bquot lexbuf ^ "`") }
  | '\''
      { RAW ("'" ^ lex_squot lexbuf ^ "'") }
  | '"'
      { RAW ("\"" ^ lex_dquot lexbuf ^ "\"") }

  (* Operator sequences are preserved as RAW text. *)
  | op as s
      { RAW s }

  (* Fallback: preserve any other single character as RAW. *)
  | any as c
      { RAW (String.make 1 c) }

  (* End of input. *)
  | eof
      { EOF }

(* Reads a backtick-quoted fragment until the closing backtick.
   The returned string does not include the outer delimiters.
   Escaped backticks (\`) are preserved as literal backticks. *)
and lex_bquot = parse
  | '`'
      { "" }
  | '\\' '`'
      { "`" ^ lex_bquot lexbuf }
  | '\\'
      { "\\" ^ lex_bquot lexbuf }
  | [^ '`' '\\']+ as s
      { s ^ lex_bquot lexbuf }

(* Reads a single-quoted fragment until the closing apostrophe.
   Escapes are preserved literally (e.g. \', \n, \t stay as two characters). *)
and lex_squot = parse
  | '\''
      { "" }
  | '\\' (any as c)
      { "\\" ^ String.make 1 c ^ lex_squot lexbuf }
  | [^ '\'' '\\']+ as s
      { s ^ lex_squot lexbuf }

(* Reads a double-quoted fragment until the closing quote.
   Escapes are preserved literally (e.g. \", \\, \n, \t).  "*)
and lex_dquot = parse
  | '"'
      { "" }
  | '\\' (any as c)
      { "\\" ^ String.make 1 c ^ lex_dquot lexbuf }
  | [^ '"' '\\']+ as s
      { s ^ lex_dquot lexbuf }
