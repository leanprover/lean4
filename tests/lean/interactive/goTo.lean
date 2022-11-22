import Lean.Elab

structure Bar where

structure Foo where
  foo₁ : Nat
  foo₂ : Nat
  bar  : Bar

def mkFoo₁ : Foo := {
--v textDocument/definition
  foo₁ := 1
    --^ textDocument/definition
--v textDocument/declaration
  foo₂ := 2
--v textDocument/typeDefinition
  bar := ⟨⟩
}

         --v textDocument/definition
#check (Bar)

structure HandWrittenStruct where
  n : Nat

-- def HandWrittenStruct.n := fun | mk n => n

          --v textDocument/definition
def hws : HandWrittenStruct := {
--v textDocument/definition
  n := 3
}

            --v textDocument/declaration
def mkFoo₂ := mkFoo₁

syntax (name := elabTest) "test" : term

@[term_elab elabTest] def elabElabTest : Lean.Elab.Term.TermElab := fun orig _ => do
  let stx ← `(2)
  Lean.Elab.Term.withMacroExpansion orig stx $ Lean.Elab.Term.elabTerm stx none

     --v textDocument/declaration
set_option trace.Elab.step true in
#check test
     --^ textDocument/definition

def temp := test

#print temp

def Baz (α : Type) := α

#check fun (b : Baz Nat) => b
                          --^ textDocument/typeDefinition

example : Nat :=
  let a := 1
--v textDocument/definition
  a + b
    --^ textDocument/definition
where
  b := 2

macro_rules | `(test) => `(3)
#check test
     --^ textDocument/definition

class Foo2 where
  foo : Nat → Nat
  foo' : Nat

class Foo3 [Foo2] where
  foo : [Foo2] → Nat

class inductive Foo4 : Nat → Type where
| mk : Nat → Foo4 0

instance : Foo2 := .mk id 0
instance : Foo3 := .mk 0

#check Foo2.foo 2
          --^ textDocument/definition
#check Foo2.foo
          --^ textDocument/definition
#check Foo2.foo'
          --^ textDocument/definition
#check @Foo2.foo
           --^ textDocument/definition

#check Foo3.foo
          --^ textDocument/definition

-- duplicate definitions link to the original
def mkFoo₁ := 1
     --^ textDocument/definition
