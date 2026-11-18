import Lean

/-!
Derives `Repr`, `BEq` and `Hashable` on a large mutual block: a hub `H` with `n` constructors
`cᵢ : Tᵢ → H`, where each structure `Tᵢ` points back to `H`. Deriving handlers used to generate the
whole block's auxiliary functions once per type, which made this quadratic in `n`.
-/

set_option Elab.async false

open Lean Elab Command Parser.Command

structure Meta where
  a : Nat
  deriving Repr, BEq, Hashable

set_option hygiene false in
/-- Elaborates the mutual block, with `n` hub constructors. -/
elab "#mutual_block" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 40 else 10
  let ts := (Array.range n).map fun i => mkIdent (.mkSimple s!"T{i}")
  let mut ctors ← ts.mapIdxM fun i t => `(ctor| | $(mkIdent (.mkSimple s!"c{i}")):ident : $t → H)
  ctors := ctors.push (← `(ctor| | other (a : Option Meta) (s : String) : H))
  let hub ← `(inductive H where
      $ctors:ctor*
      deriving Repr, BEq, Hashable)
  let h2 ← `(structure H2 where
      p : Option Meta := none
      f1 : H
      f2 : String
      deriving Repr, BEq, Hashable)
  let structs ← ts.mapM fun t => `(structure $t:ident where
      p : Option Meta := none
      f1 : H
      f2 : Array H2
      deriving Repr, BEq, Hashable)
  let decls : Array Command := #[hub, h2] ++ structs
  elabCommand (← `(mutual $decls:command* end))

#mutual_block

example : Repr T0 := inferInstance
example : BEq H := inferInstance
example : Hashable H2 := inferInstance
