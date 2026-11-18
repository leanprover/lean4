import Lean

/-!
Benchmark: a `do` block of `n` pairs `let pᵢ ← pure ⟨i, i⟩; let _qᵢ : Nat × Nat := pᵢ`.
The anonymous constructor in every `pᵢ` postpones until the next statement fixes the type of `pᵢ`.
-/

open Lean Elab Command

set_option maxRecDepth 100000

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 60 else 5
  let ps := (Array.range n).map fun i => mkIdent (.mkSimple s!"p{i}")
  let items ← (Array.range n).foldlM (init := #[]) fun items i => do
    let p := ps[i]!
    let q := mkIdent (.mkSimple s!"_q{i}")
    return items.push (← `(Parser.Term.doSeqItem| let $p:ident ← pure ⟨$(quote i), $(quote i)⟩))
      |>.push (← `(Parser.Term.doSeqItem| let $q:ident : Nat × Nat := $p))
  elabCommand (← `(noncomputable def $(mkIdent `f) : StateM Nat (Nat × Nat) := do
    $items*
    pure $(ps.back!)))

#bench
