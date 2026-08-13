import Std.Tactic.Do
import Std.WP

/-!
A spec whose program applies a continuation variable under a binder, as in
`Lang.bnd (fun x => Lang.add (k x) (Lang.nat 0))`. First-order matching leaves `k` open, so
applying the spec to `Lang.bnd (fun x => Lang.add (Lang.nat x) (Lang.nat 0))` solves `k` while the
pending unification constraints are processed, i.e. after the emitted goal's type was built. That
goal's program is the metavariable standing for `k`, applied to `5`, and `vcgen` continues by
instantiating it.
-/

set_option mvcgen.warning false

open Std.WP
open Lean.Order

inductive Lang where
  | nat (n : Nat)
  | add (l r : Lang)
  /-- Runs its body at `5`. -/
  | bnd (k : Nat → Lang)

inductive IsValue : Lang → Prop where
  | nat : IsValue (.nat _n)

def Value : Type _ := { l : Lang // IsValue l }

axiom wp : Lang → (Value → Prop) → Prop
axiom wp_mono : ∀ (post post' : Value → Prop),
  (∀ (x : Value), post x → post' x) → wp x post → wp x post'
axiom wp_nat : ∀ {n : Nat} {Φ : Value → Prop}, Φ ⟨.nat n, .nat⟩ → wp (Lang.nat n) Φ
axiom wp_add : ∀ {l r : Lang} {Φ : Value → Prop},
  wp l (fun vl => wp r (fun vr => ∀ nl nr,
    vl.val = Lang.nat nl → vr.val = Lang.nat nr → Φ ⟨.nat (nl + nr), .nat⟩)) →
  wp (Lang.add l r) Φ
axiom wp_bnd : ∀ {k : Nat → Lang} {Φ : Value → Prop},
  wp (Lang.add (k 5) (Lang.nat 0)) Φ →
  wp (Lang.bnd (fun x => Lang.add (k x) (Lang.nat 0))) Φ

instance instWP_Lang : WP Lang Value Prop EPost.Nil where
  wpTrans l := ⟨fun Φ _ => wp l Φ⟩
  wp_trans_monotone x := by
    simp [PredTrans.monotone, Lean.Order.PartialOrder.rel]
    intros; apply wp_mono <;> trivial

@[spec]
theorem spec_nat {n : Nat} {Φ : Value → Prop} : ⦃ Φ ⟨.nat n, .nat⟩ ⦄ (Lang.nat n) ⦃ Φ; epost⟨⟩⦄ :=
  Triple.iff.mpr wp_nat

@[spec]
theorem spec_add {l r} {Φ : Value → Prop} :
    ⦃ Std.WP.wp l
        (fun vl => Std.WP.wp r
          (fun vr => ∀ nl nr, vl.val = Lang.nat nl → vr.val = Lang.nat nr →
            Φ ⟨.nat (nl + nr), .nat⟩) epost⟨⟩) epost⟨⟩ ⦄
      (Lang.add l r) ⦃ Φ; epost⟨⟩⦄ := by
  refine Triple.iff.mpr ?_
  simp only [Lean.Order.le_prop_eq_imp]
  intro h; exact wp_add h

@[spec]
theorem spec_bnd {k : Nat → Lang} {Φ : Value → Prop} :
    ⦃ Std.WP.wp (Lang.add (k 5) (Lang.nat 0)) Φ epost⟨⟩ ⦄
      (Lang.bnd (fun x => Lang.add (k x) (Lang.nat 0))) ⦃ Φ; epost⟨⟩⦄ := by
  refine Triple.iff.mpr ?_
  simp only [Lean.Order.le_prop_eq_imp]
  intro h; exact wp_bnd h

example : ⦃ True ⦄ Lang.bnd (fun x => Lang.add (Lang.nat x) (Lang.nat 0))
    ⦃ fun v => v.val = Lang.nat 5 ⦄ := by
  vcgen <;> grind
