import Lean

/-!
Derives `Repr`, `BEq` and `Hashable` on a large mutual block: a hub `H` with `n` constructors
`cᵢ : Tᵢ → H`, where each structure `Tᵢ` points back to `H`. Deriving handlers used to generate the
whole block's auxiliary functions once per type, which made this quadratic in `n`.
-/

set_option Elab.async false

open Lean Elab Command

structure Meta where
  a : Nat
  deriving Repr, BEq, Hashable

/-- Elaborates the mutual block, with `n` hub constructors. -/
elab "#mutual_block" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 40 else 10
  let is := List.range n
  let derivs := "  deriving Repr, BEq, Hashable\n"
  let ctors := String.join <| is.map fun i => s!"  | c{i} : T{i} → H\n"
  let structs := String.join <| is.map fun i =>
    s!"structure T{i} where\n  p : Option Meta := none\n  f1 : H\n  f2 : Array H2\n{derivs}"
  let src := s!"mutual\ninductive H where\n{ctors}  | other (a : Option Meta) (s : String) : H\n{derivs}\
    structure H2 where\n  p : Option Meta := none\n  f1 : H\n  f2 : String\n{derivs}{structs}end"
  elabCommand (← ofExcept <| Parser.runParserCategory (← getEnv) `command src)

#mutual_block

example : Repr T0 := inferInstance
example : BEq H := inferInstance
example : Hashable H2 := inferInstance
