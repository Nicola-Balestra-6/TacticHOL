/* lib/grammar/tactic_parser.mly */

%{
  open Tactic_ast
  let ( @ ) = List.append
%}

%token THEN THENL ORELSE TRY REPEAT LET IN
%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE SEMI
%token <string> RAW
%token EOF

/* Artificial precedence for let ... in ... */
%nonassoc LETIN

/* ORELSE binds less tightly than THEN / THENL. */
%left ORELSE
%left THEN THENL

%start <Tactic_ast.t> main
/* val main: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> Tactic_ast.t */

%%

/* Entry point: parse a full tactic expression followed by EOF. */
main:
  | e = expr EOF
      { e }

/* Main expression level: infix tactic combinators. */
expr:
  | a = expr ORELSE b = expr
      { Orelse (a, b) }
  | a = expr THEN b = expr
      { Then (a, b) }
  | a = expr THENL bs = thenl_list
      { Thenl (a, bs) }
  | p = prefix
      { p }

/* Prefix forms: TRY, REPEAT, and let ... in ... */
prefix:
  | TRY p = prefix
      { Try p }
  | REPEAT p = prefix
      { Repeat p }
  | LET bind = let_bind IN e = expr %prec LETIN
      { LetIn (bind, e) }
  | a = atom
      { a }

/* Atomic expressions: either parenthesized structure or a raw leaf. */
atom:
  | LPAREN e = expr RPAREN
      { Paren e }
  | l = leaf
      { l }

/* THENL expects a bracketed list of tactic expressions. */
thenl_list:
  | LBRACK es = expr_list RBRACK
      { es }

/* Non-empty list of expressions separated by semicolons. */
expr_list:
  | e = expr
      { [ e ] }
  | e = expr SEMI es = expr_list
      { e :: es }

/* A leaf is a raw fragment represented as a list of string chunks. */
leaf:
  | x = leaf_head xs = raw_seq_tail
      { Leaf (x @ xs) }

/* A leaf must not start with LPAREN.
   This avoids ambiguity with:
     atom -> LPAREN expr RPAREN
*/
leaf_head:
  | s = RAW
      { [ s ] }
  | LBRACK xs = raw1 RBRACK
      { [ "[" ] @ xs @ [ "]" ] }
  | LBRACE xs = raw1 RBRACE
      { [ "{" ] @ xs @ [ "}" ] }

/* Non-empty raw sequence, used for let-bindings and leaf tails. */
raw_seq:
  | x = raw_item xs = raw_seq_tail
      { x @ xs }

/* Optional continuation of a raw sequence. */
raw_seq_tail:
  |
      { [] }
  | x = raw_item xs = raw_seq_tail
      { x @ xs }

/* A single raw item.
   Parentheses, brackets, and braces are preserved as literal string chunks
   when they appear inside raw contexts. */
raw_item:
  | s = RAW
      { [ s ] }
  | LPAREN xs = raw1 RPAREN
      { [ "(" ] @ xs @ [ ")" ] }
  | LBRACK xs = raw1 RBRACK
      { [ "[" ] @ xs @ [ "]" ] }
  | LBRACE xs = raw1 RBRACE
      { [ "{" ] @ xs @ [ "}" ] }

/* Inner raw content inside (...), [...], or {...}. */
raw1:
  |
      { [] }
  | x = raw1_item xs = raw1
      { x @ xs }

/* Some lexer-level keywords must be converted back to raw text in raw contexts. */
raw_kw:
  | IN
      { "in" }

/* Items allowed inside inner raw content. */
raw1_item:
  | x = raw_item
      { x }
  | s = raw_kw
      { [ s ] }
  | SEMI
      { [ ";" ] }

/* let-binding content is kept as raw text rather than parsed structurally. */
let_bind:
  | xs = raw_seq
      { xs }
