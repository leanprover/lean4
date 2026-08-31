import Lean
open Lean Lean.Meta

def Set (α : Type) : Type :=
  α → Prop

def Set.empty {α : Type} : Set α :=
  fun _ => False

def Set.insert (s : Set α) (a : α) : Set α :=
  fun x => x = a ∨ s a

#eval do
  let insertType ← inferType (mkConst `Set.insert)
  let ⟨_, _, resultType⟩ ← forallMetaBoundedTelescope insertType 3
  println! "{resultType}"
