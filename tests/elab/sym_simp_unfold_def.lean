import Lean
/-!
Tests that `Sym.simp` unfolds definitions using their equational theorems when a
function symbol is provided as a parameter, like `Meta.simp` does with `simp [f]`.
-/

def f (a : Nat) := a + a

-- Non-recursive definition: `simp [f]` uses `f.eq_1`
example : f 2 = 4 := by
  sym =>
    simp [f]

-- Recursive definition defined by pattern matching
def g : Nat → Nat
  | 0 => 1
  | n+1 => g n + 1

example : g 2 = 3 := by
  sym =>
    simp [g]

-- Prop-valued definition: unfolds to its value
def myDef : Prop := True

example : myDef := by
  sym =>
    simp [myDef]

-- Definitions also work in the `rewrite [...]` simproc DSL
register_sym_simp unfoldF where
  post := ground >> rewrite [f]

example : f 2 = 4 := by
  sym =>
    simp unfoldF
