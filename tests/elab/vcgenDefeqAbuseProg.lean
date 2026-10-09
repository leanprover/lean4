import Std.WP
import Std.WP.Triple.SpecLemmas

/-!
# `vcgen` on a program that is not of the type of its `WP` instance

**This test abuses definitional equality.** The programs below have type `Exp`, but their `WP`
instance is for `Tagged n Exp`. The two types are definitionally equal, so every triple and every
`wp` must name its program type explicitly with `(Prog := Tagged n Exp)`. Programs normally have
the program type of their `WP` instance.

`vcgen` supports such abuse as far as `SymM` permits. It builds spec rules from the `Prog` and `WP`
instance arguments of the goal's `wp` application, never from the type of the program. The
assertion type `Fin (n + 1) → Prop` depends on `n`, so the type `Exp` of the program determines no
`WP` instance.
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
