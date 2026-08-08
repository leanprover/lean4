import Lean
open Lean PrettyPrinter

def fmt (stx : CoreM Syntax) : CoreM Format := do PrettyPrinter.ppTerm ⟨← stx⟩

#eval fmt `(if c then do t else e)
#eval fmt `(if c then do t; t else e)
#eval fmt `(if c then do t else do e)
#eval fmt `(if let x := c then do t else do e)
#eval fmt `(if c then do t else if c then do t else do e) -- FIXME: make this cascade better?
#eval fmt `(do if c then t else e)
#eval fmt `(do if c then t else if c then t else e)
#eval fmt `(do for x in xs do pure ())
#eval fmt `(do let mut acc := 0; for x in xs do acc := acc + x; return acc)
#eval fmt `(do while c do pure ())
#eval fmt `(do unless c do pure ())
-- intrinsic-verification clauses: `invariant` inline with the loop, `requires`/`ensures` inline with `def`
#eval fmt `(do assert 0 ≤ acc)
#eval fmt `(do assert s => s ≤ acc)
#eval fmt `(do for x in xs invariant pref suff => 0 ≤ acc do pure ())
#eval fmt `(do for x in xs invariant pref suff s => s ≤ acc do pure ())
#eval fmt `(command| def clampLow (n lo : Nat) : Id Nat requires lo ≤ n ensures r => r = n := pure n)
#eval fmt `(command| def k (x : Nat) requires s => s > x ensures r => r ≥ x := pure x)
#eval fmt `(command| def g (x : Nat) requires x > 0 ensures r => r ≥ x := pure x)
#eval fmt `(command| def m (x : Nat) requires x > 0 ensures | 0 => False | (n+1) => n ≥ x := pure x)
#eval fmt `(command| def h (x : Nat) : Id Nat ensures r => r = x := pure x
where finally
  | spec => skip)

#eval fmt `(def foo := by
  · skip; skip
  · skip; skip
    skip
    (skip; skip)
    (skip; skip
     try skip; skip
     try skip
         skip
     skip))

#eval fmt `(by
  try
  skip
  skip)

set_option format.indent 3 in
#eval fmt `(by
  try
  skip
  skip)
set_option format.indent 4 in
#eval fmt `(by
  try
  skip
  skip)
set_option format.indent 4 in
#eval fmt `(by
  try
    skip
    skip
  skip)

#eval fmt `({
  foo := bar
  bar := foo + bar
})

#eval fmt `(let x := { foo := bar
                       bar := foo + bar }
            x)

#eval fmt `(command|
def foo : a b c d e f g a b c d e f g h where
  h := 42
  i := 42
  j := 42
  k := 42)

#eval fmt `(calc
  1 = 1 := rfl
  1 = 1 := rfl)

#eval fmt `(by rw [] at h)
