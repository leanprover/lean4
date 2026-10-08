import Std.WP
import Std.WP.Triple.SpecLemmas

/-!
# `vcgen` on a program type that is a `def` synonym

The program type `Tagged n Exp` unfolds to `Exp`, so a program `e : Exp` also serves as a program of
type `Tagged n Exp`. Only `Tagged n Exp` has a `WP` instance. Its assertion type
`Fin (n + 1) → Prop` depends on `n`, so the instance cannot be found from `Exp`. `vcgen` builds the
spec rules from the `Prog` and `WP` instance arguments of the goal's `wp` application.
-/

open Std.WP
open Lean.Order

set_option experimental.vcgen true

inductive Exp where
  | lit (k : Nat)
  | add (a b : Exp)

def Exp.eval : Exp → Nat
  | .lit k => k
  | .add a b => a.eval + b.eval

def Tagged (_n : Nat) (α : Type) := α

instance : WP (Tagged n Exp) Nat (Fin (n + 1) → Prop) EStack⟨⟩ where
  trans e := ⟨fun Q _ i => Q (Exp.eval e) i⟩
  trans_monotone _ := by
    intro Q Q' _ _ _ hQ i h
    exact hQ _ i h

variable {n : Nat} {Q : Nat → Fin (n + 1) → Prop} {eposts : EStack⟨⟩}

@[spec] theorem Spec.lit (k : Nat) :
    Triple (Prog := Tagged n Exp) (Exp.lit k) (Q k) Q eposts :=
  Triple.iff.mpr fun _ h => h

@[spec] theorem Spec.add (a b : Exp) :
    Triple (Prog := Tagged n Exp) (Exp.add a b)
      (wp (Prog := Tagged n Exp) a
        (fun x => wp (Prog := Tagged n Exp) b (fun y => Q (x + y)) eposts) eposts)
      Q eposts :=
  Triple.iff.mpr fun _ h => h

example :
    Triple (Prog := Tagged 3 Exp) (Exp.add (.lit 1) (.lit 2)) (fun _ => True) (fun r _ => r = 3) ⊥ := by
  vcgen
