import Std.Tactic.Do
import Std.WP

/-!
`vcgen` weakens the exception postcondition of a spec along the `AssertionHom` instance of the
exception postcondition type. `Thrown` is such a type outside the stack hierarchy: the
verification condition for a concrete exception postcondition is stated for the factor of the
stack that `Thrown` converts to, and a schematic factor is assigned instead of yielding a
verification condition.
-/

set_option mvcgen.warning false
open Std.WP Lean.Order

/-- The exception postcondition of a `Prog`: what holds of the thrown message. -/
structure Thrown where
  /-- The assertion about the thrown message. -/
  onThrow : String → Prop

instance : PartialOrder Thrown where
  rel p q := p.onThrow ⊑ q.onThrow
  rel_refl := PartialOrder.rel_refl
  rel_trans h₁ h₂ := PartialOrder.rel_trans h₁ h₂
  rel_antisymm h₁ h₂ := congrArg Thrown.mk (PartialOrder.rel_antisymm h₁ h₂)

instance : CompleteLattice Thrown where
  has_sup c :=
    let ⟨sup, hsup⟩ := CompleteLattice.has_sup (fun f => c ⟨f⟩)
    ⟨⟨sup⟩, fun q =>
      ⟨fun hq p hp => (hsup q.onThrow).mp hq p.onThrow hp,
       fun h => (hsup q.onThrow).mpr fun f hf => h ⟨f⟩ hf⟩⟩

instance : AssertionHom Thrown EStack⟨String → Prop⟩ (fun t => estack⟨t.onThrow⟩) where
  le_of_hom_le h := h.1
  hom_bot := by
    have h : (⊥ : Thrown).onThrow = ⊥ :=
      PartialOrder.rel_antisymm (bot_le (⟨⊥⟩ : Thrown)) (bot_le _)
    rw [h, Subsingleton.elim EStackEnd.mk (⊥ : EStackEnd), Prod.mk_bot]

/-- A program that returns or throws a message. -/
inductive Prog (α : Type) where
  | ret (a : α)
  | throw (e : String)

instance : WP (Prog α) α Prop Thrown where
  wpTrans
    | .ret a => ⟨fun post _ => post a⟩
    | .throw e => ⟨fun _ epost => epost.onThrow e⟩
  wp_trans_monotone
    | .ret _ => fun _ _ _ _ _ hpost => hpost _
    | .throw e => fun _ _ _ _ hepost _ => hepost e

axiom Q : String → Prop

def boom : Prog Unit := .throw "boom"

def boom' : Prog Unit := .throw "boom"

/-- Exception postcondition with a concrete assertion. -/
@[spec] theorem boom_spec {post : Unit → Prop} :
    ⦃True⦄ boom ⦃post; (⟨fun e => e = "boom"⟩ : Thrown)⦄ := ⟨fun _ => rfl⟩

/-- Exception postcondition with a schematic assertion. -/
@[spec] theorem boom'_spec {post : Unit → Prop} {E : String → Prop} :
    ⦃E "boom"⦄ boom' ⦃post; (⟨E⟩ : Thrown)⦄ := ⟨PartialOrder.rel_refl⟩

/-- The concrete assertion of `boom_spec` yields the verification condition
`∀ e, e = "boom" → e = "boom" ∨ e = "crash"`. -/
example : ⦃True⦄ boom ⦃fun _ => True; (⟨fun e => e = "boom" ∨ e = "crash"⟩ : Thrown)⦄ := by
  vcgen
  grind

/-- The schematic assertion of `boom'_spec` is assigned the assertion of the goal, so no
verification condition remains: the precondition VC closes by reflexivity. -/
example : ⦃Q "boom"⦄ boom' ⦃fun _ => True; (⟨Q⟩ : Thrown)⦄ := by
  vcgen
