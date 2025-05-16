/-!
# Allow postponing coercion/defeq if there are mvars
-/

abbrev Pred (σs : List Type) := match σs with
  | [] => Prop
  | σ::σs => σ → Pred σs

def trp {α : Type} {σs : List Type} (P Q : α → Pred σs) : Prop := sorry

theorem spec {α : Type} {σs : List Type} {a : α} (P : α → Pred σs) :
  trp P P := sorry

/--
info: spec fun p s =>
  p.fst = some p.snd ∧ s = 4 : trp (fun p s => p.fst = some p.snd ∧ s = 4) fun p s => p.fst = some p.snd ∧ s = 4
-/
#guard_msgs in
#check (spec (σs := [Nat]) (fun p s => p.1 = p.2 ∧ s = 4)
        : @trp (MProd (Option Nat) Nat) [Nat] _ _)

/-!
This used to have a failure on `(fun p s => p.1 = p.2 ∧ s = 4)`
-/
/--
info: spec fun p s =>
  p.fst = some p.snd ∧ s = 4 : trp (fun p s => p.fst = some p.snd ∧ s = 4) fun p s => p.fst = some p.snd ∧ s = 4
-/
#guard_msgs in
#check (spec (fun p s => p.1 = p.2 ∧ s = 4)
        : @trp (MProd (Option Nat) Nat) [Nat] _ _)
