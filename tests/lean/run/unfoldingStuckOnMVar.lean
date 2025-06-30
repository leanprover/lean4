/-!
# Definitional equality on a definition the unfolding of which is stuck on an MVar
-/

namespace One

def Pred (σs : List Type) := match σs with
  | [] => Prop
  | σ::σs => σ → Pred σs

def Blah (x : Nat) := x

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
This used to have a failure on `(fun p s => p.1 = p.2 ∧ s = 4)` because the definitional equality
  ?m.547 p → Prop =?= Pred ?m.504
used to return `false` instead of being stuck on `?m.504`.
-/
set_option trace.Meta.isDefEq.stuckMVar true in
/--
info: spec fun p s =>
  p.fst = some p.snd ∧ s = 4 : trp (fun p s => p.fst = some p.snd ∧ s = 4) fun p s => p.fst = some p.snd ∧ s = 4
---
trace: [Meta.isDefEq.stuckMVar] found stuck MVar ?m.504 : List Type
[Meta.isDefEq.stuckMVar] found stuck MVar ?m.504 : List Type
-/
#guard_msgs in
#check (spec (fun p s => p.1 = p.2 ∧ s = 4)
        : @trp (MProd (Option Nat) Nat) [Nat] _ _)

end One

namespace I8766


def SPred (σs : List Type) := match σs with
  | [] => Prop
  | σ :: σs => σ → SPred σs

class WP (m : Type → Type) (σs : outParam (List Type)) where

instance : WP (EStateM ε σ) [σ] where

def Triple [WP m σs] (x : m α) (P Q : SPred σs) := True

/-!
Similarly to the above, reduction of `SPred ?m.1250` is stuck on `?m.1250`.
It will eventually be solved once `WP (EStateM ε σ) [σ]` has been synthesized.
-/
set_option trace.Meta.isDefEq.stuckMVar true in
/--
info: ∀ (ε σ α : Type) (s : σ) (prog : EStateM ε σ α) (P : σ → Prop), Triple prog (fun s' => s' = s) P → P s : Prop
---
trace: [Meta.isDefEq.stuckMVar] found stuck MVar ?m.1208 : List Type
[Meta.isDefEq.stuckMVar] found stuck MVar ?m.1208 : List Type
---
trace: [Meta.isDefEq.stuckMVar] found stuck MVar ?m.1208 : List Type
[Meta.isDefEq.stuckMVar] found stuck MVar ?m.1208 : List Type
[Meta.isDefEq.stuckMVar] found stuck MVar ?m.1208 : List Type
-/
#guard_msgs in
#check ∀ ε σ α s (prog : EStateM ε σ α) (P : σ → Prop),
    Triple prog (fun s' => s' = s) P → P s

end I8766
