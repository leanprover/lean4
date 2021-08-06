import Lean
open Lean Lean.Meta

def Set (α : Type) : Type :=
  α → Prop

def Set.empty {α : Type} : Set α :=
  fun a => False

def Set.insert (s : Set α) (a : α) : Set α :=
  fun x => x = a ∨ s a

#eval show MetaM Unit from do
  let insertType ← inferType (mkConst `Set.insert)
  let ⟨mvars, bInfos, resultType⟩ ← forallMetaBoundedTelescope insertType 3
  println! "{resultType}"
