import Lean
/-!
`simp` meets a `match` with many alternatives that it cannot reduce, because the discriminant is a
local variable: `Op.effect.eq_def` unfolds `Op.effect` in the step function
`fun t op => op.effect t` of `List.foldl`. None of the `match` equation theorems can rewrite it.
(`Op.effect.eq_def` is used because generating the equation theorems of `Op.effect`, as
`simp [Op.effect]` would do, generates the `match` equation theorems anyway.)
-/
open Lean Elab Command

set_option Elab.async false

elab "#gen_ops" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 500 else 50
  let ctors := " ".intercalate <| (List.range n).map (s!"| o{·}")
  let alts := "\n".intercalate <| (List.range n).map fun i => s!"  | .o{i}, s => s + {i}"
  for src in [s!"inductive Op where {ctors}", s!"def Op.effect : Op → Nat → Nat\n{alts}"] do
    match Parser.runParserCategory (← getEnv) `command src with
    | .ok stx => elabCommand stx
    | .error e => throwError e

#gen_ops

def block (ops : List Op) (s : Nat) : Nat := ops.foldl (fun t op => op.effect t) s

theorem block_eq (s : Nat) : block [.o1, .o2, .o3] s = s + 1 + 2 + 3 := by
  simp [block, Op.effect.eq_def]
