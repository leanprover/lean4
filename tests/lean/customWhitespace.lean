import Lean

declare_syntax_cat ws

open Lean Parser

def myWhitespace : TokenParserFn := fun c s =>
  takeWhileFn (fun c => c.isWhitespace || c == '#') c s

def myTerm : Parser where
  fn := adaptUncacheableContextFn (fun ctx => { ctx with
      whitespaceFn := myWhitespace
      tokenFn := fun c s =>
        -- NOTE: handles identifiers only
        let startPos := s.pos
        let s := takeWhile1Fn (·.isAlpha) "" c s
        pushToken (fun ss info => mkIdent info ss ss.toString) startPos myWhitespace c s
    }) (categoryParserFn `term)

attribute [combinator_formatter myTerm] PrettyPrinter.Formatter.pushNone.formatter
attribute [combinator_parenthesizer myTerm] PrettyPrinter.Parenthesizer.pushNone.parenthesizer

macro "`[myTerm|" e:myTerm "]" : term => return ⟨e.raw⟩

#check `[myTerm| id#id # id## #]
