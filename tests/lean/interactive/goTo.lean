import Lean.Elab
--^ waitForILeans
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
  Lean.Elab.withMacroExpansionInfo orig stx $ Lean.Elab.Term.elabTerm stx none

     --v textDocument/declaration
#check test
     --^ textDocument/definition

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

def Foo4.foo : [Foo4 n] → Nat
| .mk n => n

class Foo5 where
  foo : Foo2


instance : Foo2 := .mk id 0
instance : Foo3 := .mk 0
instance : Foo4 0 := .mk 0
instance [foo2 : Foo2] : Foo5 := .mk foo2

-- should go-to instance
              --v textDocument/definition
#check Foo2.foo  2
          --^ textDocument/definition
#check (Foo2.foo)
           --^ textDocument/definition
#check (Foo2.foo')
           --^ textDocument/definition

-- should go-to projection
#check @Foo2.foo
           --^ textDocument/definition

-- test that the correct instance index is extracted
#check (Foo3.foo)
           --^ textDocument/definition

-- non-projections should not go-to instance
#check (Foo4.foo)
           --^ textDocument/definition

set_option pp.all true in
-- test that multiple instances can be extracted
#check (Foo5.foo)
           --^ textDocument/definition

-- duplicate definitions link to the original
def mkFoo₁ := 1
     --^ textDocument/definition
