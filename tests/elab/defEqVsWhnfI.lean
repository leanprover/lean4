import Lean

class CountParts_ (S : Type u) where
  μ : Type v
  α : Type w
  φ : S → μ → α

instance : CountParts_ String where
  μ := Char
  α := Nat
  φ haystack needle := haystack.foldl (fun acc x => acc + if x == needle then 1 else 0) 0

class CountParts (S : Type u) (μ : Type v) (α : Type w) where
  φ : S → μ → α

open Lean Elab Meta Term in
def test : TermElabM Unit := do
  let e ← elabTerm (← `(CountParts_.α String)) none
  let nat := Lean.mkConst ``Nat
  assert! (← whnf e) == nat
  assert! (← whnfI e) == nat
  assert! (← whnfR e) != nat
  assert! (← isDefEq e nat)
  assert! (← withReducibleAndInstances <| isDefEq e nat)
  assert! !(← withReducible <| isDefEq e nat)
