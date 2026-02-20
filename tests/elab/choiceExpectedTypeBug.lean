import Lean



structure A :=
(x : Nat := 10)

def f : A :=
{ }

theorem ex : f = { x := 10 } :=
rfl

#check f

syntax (name := emptyS) "⟨" "⟩"  : term -- overload `⟨ ⟩` notation

open Lean
open Lean.Elab
open Lean.Elab.Term

@[term_elab emptyS] def elabEmptyS : TermElab :=
fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  let stxNew ← `(Nat.zero)
  withMacroExpansion stx stxNew $
    elabTerm stxNew expectedType?

def foo (x : Unit) := x

def f1 : Unit :=
let x := ⟨ ⟩
foo x

def f2 : Unit :=
let x := ⟨ ⟩
x

def f3 : Nat :=
let x := ⟨ ⟩
x

theorem ex2 : f3 = 0 :=
rfl
