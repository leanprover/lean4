import Std.Tactic.Do
import Std.Internal.Do

/-!
`vcgen` must split a raw `∀`/`→` on the RHS of a `Prop` entailment (`le_forall`) and an `iInf` on
any `Pi` assertion lattice (`iInf_apply` + `le_iInf`), including when the `iInf` is applied to excess
state arguments.
-/

set_option mvcgen.warning false

open Std.Internal.Do
open Lean.Order

/-! ## Raw `∀` on the `Prop` lattice -/

inductive Lang where
  | nat (n : Nat)
  | add (l r : Lang)

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
    ⦃ Std.Internal.Do.wp l
        (fun vl => Std.Internal.Do.wp r
          (fun vr => ∀ nl nr, vl.val = Lang.nat nl → vr.val = Lang.nat nr →
            Φ ⟨.nat (nl + nr), .nat⟩) epost⟨⟩) epost⟨⟩ ⦄
      (Lang.add l r) ⦃ Φ; epost⟨⟩⦄ := by
  refine Triple.iff.mpr ?_
  simp only [Lean.Order.le_prop_eq_imp]
  intro h; exact wp_add h

example : ⦃ True ⦄ Lang.add (.add (.nat 1) (.nat 2)) (.nat 3) ⦃ fun v => v.val = Lang.nat 6 ⦄ := by
  vcgen <;> grind

/-! ## `iInf` on a `Pi` assertion lattice, with excess state arguments -/

/-- Separate program type so the `Nat → Prop` `WP` instance does not compete with `instWP_Lang`. -/
inductive LangS where
  | nat (n : Nat)
  | add (l r : LangS)

inductive IsValueS : LangS → Prop where
  | nat : IsValueS (.nat _n)

def ValueS : Type _ := { l : LangS // IsValueS l }

axiom wpS : LangS → (ValueS → Nat → Prop) → Nat → Prop
axiom wpS_mono : ∀ (x : LangS) (post post' : ValueS → Nat → Prop),
  (∀ v s, post v s → post' v s) → ∀ s, wpS x post s → wpS x post' s
axiom wpS_nat : ∀ {n : Nat} {Φ : ValueS → Nat → Prop} {s : Nat},
  Φ ⟨.nat n, .nat⟩ s → wpS (LangS.nat n) Φ s
axiom wpS_add : ∀ {l r} {Φ : ValueS → Nat → Prop} {s : Nat},
  wpS l (fun vl s => wpS r (fun vr s =>
    (iInf fun nl => iInf fun nr =>
      ⌜vl.val = LangS.nat nl⌝ ⇨ ⌜vr.val = LangS.nat nr⌝ ⇨ Φ ⟨.nat (nl + nr), .nat⟩) s) s) s →
  wpS (LangS.add l r) Φ s

instance instWP_LangS : WP LangS ValueS (Nat → Prop) EPost.Nil where
  wpTrans l := ⟨fun Φ _ => wpS l Φ⟩
  wp_trans_monotone x := by
    simp [PredTrans.monotone, Lean.Order.PartialOrder.rel]
    intros; apply wpS_mono <;> trivial

@[spec]
theorem spec_nat_s {n : Nat} {Φ : ValueS → Nat → Prop} :
    ⦃ Φ ⟨.nat n, .nat⟩ ⦄ (LangS.nat n) ⦃ Φ; epost⟨⟩⦄ := by
  refine Triple.iff.mpr ?_
  intro s hs; exact wpS_nat hs

@[spec]
theorem spec_add_s {l r} {Φ : ValueS → Nat → Prop} :
    ⦃ Std.Internal.Do.wp l
        (fun vl => Std.Internal.Do.wp r
          (fun vr => iInf fun nl => iInf fun nr =>
            ⌜vl.val = LangS.nat nl⌝ ⇨ ⌜vr.val = LangS.nat nr⌝ ⇨
              Φ ⟨.nat (nl + nr), .nat⟩) epost⟨⟩) epost⟨⟩ ⦄
      (LangS.add l r) ⦃ Φ; epost⟨⟩⦄ := by
  refine Triple.iff.mpr ?_
  intro s h; exact wpS_add h

example : ⦃ fun _ => True ⦄
    LangS.add (.add (.nat 1) (.nat 2)) (.nat 3)
    ⦃ fun v _ => v.val = LangS.nat 6 ⦄ := by
  vcgen <;> grind
