/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.NotationExtra

universes u v

/- Classical reasoning support -/

namespace Classical

axiom choice {α : Sort u} : Nonempty α → α

noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩

noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem chooseSpec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property

/- Diaconescu's theorem: excluded middle from choice, Function extensionality and propositional extensionality. -/
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p;
  let V (x : Prop) : Prop := x = False ∨ p;
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩;
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩;
  let u : Prop := choose exU;
  let v : Prop := choose exV;
  have uDef : U u := chooseSpec exU;
  have vDef : V v := chooseSpec exV;
  have notUvOrP : u ≠ v ∨ p :=
    match uDef, vDef with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := hvf.symm ▸ hut.symm ▸ trueNeFalse
      Or.inl hne
  have pImpliesUv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun a => Or.inr hp;
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun a => Or.inr hp;
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr);
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV :=
      hpred ▸ fun exU exV => rfl;
    show u = v from h₀ ..;
  match notUvOrP with
  | Or.inl hne => Or.inr (mt pImpliesUv hne)
  | Or.inr h   => Or.inl h

theorem existsTrueOfNonempty {α : Sort u} : Nonempty α → ∃ x : α, True
  | ⟨x⟩ => ⟨x, trivial⟩

noncomputable def inhabitedOfNonempty {α : Sort u} (h : Nonempty α) : Inhabited α :=
  ⟨choice h⟩

noncomputable def inhabitedOfExists {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : Inhabited α :=
  inhabitedOfNonempty (Exists.elim h (fun w hw => ⟨w⟩))

/- all propositions are Decidable -/
noncomputable scoped instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩

noncomputable def decidableInhabited (a : Prop) : Inhabited (Decidable a) where
  default := inferInstance

noncomputable def typeDecidableEq (α : Sort u) : DecidableEq α :=
  fun x y => inferInstance

noncomputable def typeDecidable (α : Sort u) : PSum α (α → False) :=
  match (propDecidable (Nonempty α)) with
  | (isTrue hp)  => PSum.inl (@arbitrary _ (inhabitedOfNonempty hp))
  | (isFalse hn) => PSum.inr (fun a => absurd (Nonempty.intro a) hn)

noncomputable def strongIndefiniteDescription {α : Sort u} (p : α → Prop) (h : Nonempty α) : {x : α // (∃ y : α, p y) → p x} :=
  @dite _ (∃ x : α, p x) (propDecidable _)
    (fun (hp : ∃ x : α, p x) =>
      show {x : α // (∃ y : α, p y) → p x} from
      let xp := indefiniteDescription _ hp;
      ⟨xp.val, fun h' => xp.property⟩)
    (fun hp => ⟨choice h, fun h => absurd h hp⟩)

/- the Hilbert epsilon Function -/

noncomputable def epsilon {α : Sort u} [h : Nonempty α] (p : α → Prop) : α :=
  (strongIndefiniteDescription p h).val

theorem epsilonSpecAux {α : Sort u} (h : Nonempty α) (p : α → Prop) : (∃ y, p y) → p (@epsilon α h p) :=
  (strongIndefiniteDescription p h).property

theorem epsilonSpec {α : Sort u} {p : α → Prop} (hex : ∃ y, p y) : p (@epsilon α (nonemptyOfExists hex) p) :=
  epsilonSpecAux (nonemptyOfExists hex) p hex

theorem epsilonSingleton {α : Sort u} (x : α) : @epsilon α ⟨x⟩ (fun y => y = x) = x :=
  @epsilonSpec α (fun y => y = x) ⟨x, rfl⟩

/- the axiom of choice -/

theorem axiomOfChoice {α : Sort u} {β : α → Sort v} {r : ∀ x, β x → Prop} (h : ∀ x, ∃ y, r x y) : ∃ (f : ∀ x, β x), ∀ x, r x (f x) :=
  ⟨_, fun x => chooseSpec (h x)⟩

theorem skolem {α : Sort u} {b : α → Sort v} {p : ∀ x, b x → Prop} : (∀ x, ∃ y, p x y) ↔ ∃ (f : ∀ x, b x), ∀ x, p x (f x) :=
  ⟨axiomOfChoice, fun ⟨f, hw⟩ (x) => ⟨f x, hw x⟩⟩

theorem propComplete (a : Prop) : a = True ∨ a = False := by
  cases em a with
  | inl _  => apply Or.inl; apply propext; apply Iff.intro; { intros; apply True.intro }; { intro; assumption }
  | inr hn => apply Or.inr; apply propext; apply Iff.intro; { intro h; exact hn h }; { intro h; apply False.elim h }

-- this supercedes byCases in Decidable
theorem byCases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
  Decidable.byCases (dec := propDecidable _) hpq hnpq

-- this supercedes byContradiction in Decidable
theorem byContradiction {p : Prop} (h : ¬p → False) : p :=
  Decidable.byContradiction (dec := propDecidable _) h

macro "byCases" h:ident ":" e:term : tactic =>
  `(cases em $e:term with
    | inl $h:ident => _
    | inr $h:ident => _)

end Classical
