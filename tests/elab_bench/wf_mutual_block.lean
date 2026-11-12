import Lean

/-!
Defines a large `mutual` block by well-founded recursion. Each function `fᵢ` calls `f0` and
`fᵢ₋₁`, and `f0` calls the last function at a lower level. The termination measure is
lexicographic, `(lv, i, 0, 0)`. Cleaning up each termination goal used to traverse the packed
measure of the whole block, which made this quadratic in the number of functions.
-/

set_option Elab.async false
set_option maxHeartbeats 0

open Lean Elab Command

abbrev M := StateT Nat (Except String)

set_option hygiene false in
/-- Elaborates the mutual block, with `n` functions. -/
elab "#wf_mutual_block" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 60 else 15
  let f (i : Nat) := mkIdent (.mkSimple s!"f{i}")
  let rank (i : Nat) := Syntax.mkNumLit (toString i)
  let mut decls : Array Command := #[]
  decls := decls.push (← `(
    def f0 (eager : Bool) : Nat → Nat → Nat → M Nat
      | 0, _, _ => throw "x"
      | lv+1, d, e => do
        let e ← $(f (n-1)):ident eager lv d e
        pure e
    termination_by lv => (lv, 0, 0, 0)))
  decls := decls.push (← `(
    def f1 (eager : Bool) (lv : Nat) (d : Nat) (e : Nat) : M Nat := do
      let e ← f0 eager lv d e
      pure e
    termination_by (lv, 1, 0, 0)))
  for i in 2...n do
    decls := decls.push (← `(
      def $(f i) (eager : Bool) (lv : Nat) (d : Nat) (e : Nat) : M Nat := do
        let e ← f0 eager lv (d + 1) e
        let e ← $(f (i-1)):ident eager lv d e
        pure e
      termination_by (lv, $(rank i), 0, 0)))
  elabCommand (← `(mutual $decls:command* end))

#wf_mutual_block

example := @f1.eq_def
