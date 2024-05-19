import Lean

/-!
# Parser error recovery

This test is to make sure that the error recovery feature is working as intended. In particular, it
checks that certain errors in the head of a declaration (e.g. an invalid name) don't prevent further
parse errors from being reported.
-/

open Lean Parser

/-!
## Error recovery for Lean commands
-/
def "foo" (x : Nat) :  := 5

def 5 : Nat := 3

theorem yep : True := by trivial

theorem () : Nat := 99
theorem 2.4 : Nat := )
theorem "nat" : Nat := )
theorem 3 : Nat := )

opaque ((( : Nat := )

axiom "nope" : 4 = ⟩

class inductive () where
  | "" : )

inductive 44: Type where | "" : 44

inductive 44 : Type where | "" : 44

inductive 44 (n : Nat) : Type where | "" : 44

inductive 44(n : Nat) : Type where | "" : 44

inductive 44| "" : 44

inductive !!! where
  | "" (x : Nat)) : Bogus

#eval Foo.a

inductive Item.{4, 5, 6, 7, a, "foo", b, c} : Nat where
  | foo : )
  | bar : )

example := ""

/-!
## Error recovery for custom syntax

Adding recovery to Lean's term grammar doesn't work well with the primitive tools at hand
(extensibility + token tables + backtracking are a real challenge), but for DSLs it can be useful.
This tests that error recovery works for a term syntax extension.
-/

def altParen : Parser :=
  "{|" >> termParser (prec := 51) >> recover "|}" skip

macro:50 e:altParen : term => pure ⟨e.raw[1]⟩

-- These terms show multiple errors due to recovery from missing |} tokens
#eval ([ {|2 + 3] * {| 3 + |}

-- Only one error here
#eval ([ (2 + 3] * ( 3 + ) )

example := ""

/-!
## Error recovery for custom commands

This command can recover from many parse errors. Make sure that there's no arbitrary small limit by
testing a few recoveries.
-/

def nonws : Parser where
  fn :=
    andthenFn
      (andthenFn (satisfyFn (fun c => !c.isWhitespace && c != '#')) (takeWhileFn (!·.isWhitespace)))
      whitespace

def thing : Parser :=
  recover ident nonws


open Lean Elab Command in
elab "#go " xs:thing* (Lean.Parser.eoi <|> "#stop") : command => do
  let xs := toString xs
  elabCommand <| ← `(#eval s!"hey {$(quote xs)}")

-- Many errors due to recovery!
#go
hey
5
a
g
def
5
hey
(     99
  (
#stop

-- Even though the command had errors, this is still running as expected:

def x := 5
#eval x
