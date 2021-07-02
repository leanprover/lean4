import Lean -- needed for go-to elab/syntax

structure Bar where

structure Foo where
       --v textDocument/definition
  foo₁ : Nat
  foo₂ : Nat
  bar  : Bar

def mkFoo₁ : Foo := {
--v textDocument/definition
  foo₁ := 1
--v textDocument/declaration
  foo₂ := 2
--v textDocument/typeDefinition
  bar := ⟨⟩
}

--v textDocument/definition
inductive HandWrittenStruct where
  | mk (n : Nat)

--v textDocument/declaration
def HandWrittenStruct.n := fun | mk n => n

def hws : HandWrittenStruct := {
--v textDocument/definition
  n := 3
}

            --v textDocument/declaration
def mkFoo₂ := mkFoo₁

