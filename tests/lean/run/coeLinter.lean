import Lean
import Lean.Linter.Coe
open Lean

#check Lean.Linter.Coe.shouldWarnOnDeprecatedCoercions

#check coercionsBannedInCore

set_option linter.deprecatedCoercions true

structure X
structure Y

def convert (_ : X) : Y := ⟨⟩

@[deprecated convert (since := "")]
instance mycoe : Coe X Y where coe _ := ⟨⟩

def f : Option String := "hi"

def g : Array Nat := #[1, 2, 3][*...*]

def h (foo : X) : Y := foo
