import Lean

namespace ws

open Lean Parser

-- `symbol` without whitespace trimming
def wsSymbol (s : String) : Parser where
  fn := symbolFn s
  info := symbolInfo s

attribute [combinator_formatter wsSymbol] PrettyPrinter.Formatter.symbolNoAntiquot.formatter
attribute [combinator_parenthesizer wsSymbol] PrettyPrinter.Parenthesizer.symbolNoAntiquot.parenthesizer

declare_syntax_cat tok

@[tok_parser] def s := nodeWithAntiquot (anonymous := true) "s" `ws.s <| wsSymbol " "
@[tok_parser] def t := nodeWithAntiquot (anonymous := true) "t" `ws.t <| wsSymbol "\t"
@[tok_parser] def l := nodeWithAntiquot (anonymous := true) "l" `ws.l <| wsSymbol "\n"

syntax num := (s <|> t)+ l

declare_syntax_cat io

syntax (name := writeChar) s s : io
-- ...

declare_syntax_cat stack

syntax (name := pushNum) s num : stack
-- ...

declare_syntax_cat com

syntax t l io : com
syntax s stack : com
-- ...

declare_syntax_cat prog
syntax com* l l : prog

def num.decode : TSyntax ``num → Int
  | `(num| $sign $bits* $_:l) => Id.run do
    let mut num := 0
    for b in bits do
      num := num * 2 + (if b.raw.isOfKind ``s then 0 else 1)
    if sign.raw.isOfKind ``t then
      num := -num
    return num
  | _ => unreachable!

def prog.eval : TSyntax `ws.prog → IO Unit
  | `(prog| $cs:com* $_:l $_:l) => do
    let mut stack := #[]
    for c in cs do
      match c with
      | `(com| $_:t $_:l $_:s $_:s) => IO.print (Char.ofNat stack.back.toNat)
      | `(com| $_:s $_:s $n:num) => stack := stack.push (num.decode n)
      | c => throw (.userError s!"unimplemented: {c}")
  | _ => unreachable!

def wsWhitespace : TokenParserFn :=
  takeWhileFn (!·.isWhitespace)

def enterProg : Parser where
  fn := adaptUncacheableContextFn (fun ctx => { ctx with
    whitespaceFn := wsWhitespace
    tokenFn := fun c s =>
      let startPos := s.pos
      let s := satisfyFn (·.isWhitespace) "" c s
      pushToken (fun ss info => .atom info ss.toString) startPos wsWhitespace c s
  }) (andthenFn wsWhitespace (andthenFn (categoryParserFn `prog) whitespace))

attribute [combinator_formatter enterProg] PrettyPrinter.Formatter.skip.formatter
attribute [combinator_parenthesizer enterProg] PrettyPrinter.Parenthesizer.skip.parenthesizer

elab "`[ws|" c:enterProg "]" : command => do
  --logInfoAt c m!"{c.raw.formatStx}"
  prog.eval ⟨c⟩

-- from https://en.wikipedia.org/wiki/Whitespace_(programming_language)#Sample_code
`[ws|S S S T	S S T	S S S L:Push_+1001000=72='H'_onto_the_stack
T	L
S S :Output_'H';_S S S T	T	S S T	S T	L:Push_+1100101=101='e'_onto_the_stack
T	L
S S :Output_'e';_S S S T	T	S T	T	S S L:+1101100=108='l'
T	L
S S S S S T	T	S T	T	S S L:+1101100=108='l'
T	L
S S S S S T	T	S T	T	T	T	L:+1101111=111='o'
T	L
S S S S S T	S T	T	S S L:+101100=44=','
T	L
S S S S S T	S S S S S L:+100000=32=Space
T	L
S S S S S T	T	T	S T	T	T	L:+1110111=119='w'
T	L
S S S S S T	T	S T	T	T	T	L:+1101111=111='o'
T	L
S S S S S T	T	T	S S T	S L:+1110010=114='r'
T	L
S S S S S T	T	S T	T	S S L:+1101100=108='l'
T	L
S S S S S T	T	S S T	S S L=+1100100=100='d'
T	L
S S S S S T	S S S S T	L:+100001=33='!'
T	L
S S :Output_'!';_L
L
L:End_the_program ]  -- NOTE: final space is load-bearing; it prevents the closing `]` from being parsed as a ws comment
