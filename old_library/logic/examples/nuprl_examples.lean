-- Theorems/Exercises from "Logical Investigations, with the Nuprl Proof Assistant"
-- by Robert L. Constable and Anne Trostle
-- http://www.nuprl.org/MathLibrary/LogicalInvestigations/
import logic

-- 2. The Minimal Implicational Calculus
theorem thm1 {A B : Prop} : A → B → A :=
assume Ha Hb, Ha

theorem thm2 {A B C : Prop} : (A → B) → (A → B → C) → (A → C) :=
assume Hab Habc Ha,
  Habc Ha (Hab Ha)

theorem thm3 {A B C : Prop} : (A → B) → (B → C) → (A → C) :=
assume Hab Hbc Ha,
  Hbc (Hab Ha)

-- 3. False Propositions and Negation
theorem thm4 {P Q : Prop} : ¬P → P → Q :=
assume Hnp Hp,
  absurd Hp Hnp

theorem thm5 {P : Prop} : P → ¬¬P :=
assume (Hp : P) (HnP : ¬P),
  absurd Hp HnP

theorem thm6 {P Q : Prop} : (P → Q) → (¬Q → ¬P) :=
assume (Hpq : P → Q) (Hnq : ¬Q) (Hp : P),
  have Hq : Q, from Hpq Hp,
  show false, from absurd Hq Hnq

theorem thm7 {P Q : Prop} : (P → ¬P) → (P → Q) :=
assume Hpnp Hp,
  absurd Hp (Hpnp Hp)

theorem thm8 {P Q : Prop} : ¬(P → Q) → (P → ¬Q) :=
assume (Hn : ¬(P → Q)) (Hp : P) (Hq : Q),
  -- Rermak we don't even need the hypothesis Hp
  have H : P → Q, from assume H', Hq,
  absurd H Hn

-- 4. Conjunction and Disjunction
theorem thm9 {P : Prop} : (P ∨ ¬P) → (¬¬P → P) :=
assume (em : P ∨ ¬P) (Hnn : ¬¬P),
  or.elim em
    (assume Hp, Hp)
    (assume Hn, absurd Hn Hnn)

theorem thm10 {P : Prop} : ¬¬(P ∨ ¬P) :=
assume Hnem : ¬(P ∨ ¬P),
  have Hnp : ¬P, from
    assume Hp : P,
      have Hem : P ∨ ¬P, from or.inl Hp,
      absurd Hem Hnem,
  have Hem : P ∨ ¬P, from or.inr Hnp,
  absurd Hem Hnem

theorem thm11 {P Q : Prop} : ¬P ∨ ¬Q → ¬(P ∧ Q) :=
assume (H : ¬P ∨ ¬Q) (Hn : P ∧ Q),
  or.elim H
    (assume Hnp : ¬P, absurd (and.elim_left Hn) Hnp)
    (assume Hnq : ¬Q, absurd (and.elim_right Hn) Hnq)

theorem thm12 {P Q : Prop} : ¬(P ∨ Q) → ¬P ∧ ¬Q :=
assume H : ¬(P ∨ Q),
  have Hnp : ¬P, from assume Hp : P, absurd (or.inl Hp) H,
  have Hnq : ¬Q, from assume Hq : Q, absurd (or.inr Hq) H,
  and.intro Hnp Hnq

theorem thm13 {P Q : Prop} : ¬P ∧ ¬Q → ¬(P ∨ Q) :=
assume (H : ¬P ∧ ¬Q) (Hn : P ∨ Q),
  or.elim Hn
    (assume Hp : P, absurd Hp (and.elim_left H))
    (assume Hq : Q, absurd Hq (and.elim_right H))

theorem thm14 {P Q : Prop} : ¬P ∨ Q → P → Q :=
assume (Hor : ¬P ∨ Q) (Hp : P),
  or.elim Hor
    (assume Hnp : ¬P, absurd Hp Hnp)
    (assume Hq : Q, Hq)

theorem thm15 {P Q : Prop} : (P → Q) → ¬¬(¬P ∨ Q) :=
assume (Hpq : P → Q) (Hn : ¬(¬P ∨ Q)),
  have H1 : ¬¬P ∧ ¬Q, from thm12 Hn,
  have Hnp : ¬P, from mt Hpq (and.elim_right H1),
  absurd Hnp (and.elim_left H1)

theorem thm16 {P Q : Prop} : (P → Q) ∧ ((P ∨ ¬P) ∨ (Q ∨ ¬Q)) → ¬P ∨ Q :=
assume H : (P → Q) ∧ ((P ∨ ¬P) ∨ (Q ∨ ¬Q)),
  have Hpq : P → Q, from and.elim_left H,
  or.elim (and.elim_right H)
    (assume Hem1 : P ∨ ¬P, or.elim Hem1
      (assume Hp : P, or.inr (Hpq Hp))
      (assume Hnp : ¬P, or.inl Hnp))
    (assume Hem2 : Q ∨ ¬Q, or.elim Hem2
      (assume Hq : Q, or.inr Hq)
      (assume Hnq : ¬Q, or.inl (mt Hpq Hnq)))

-- 5. First-Order Logic: All and Exists
section
variables {T : Type} {C : Prop} {P : T → Prop}
theorem thm17a : (C → ∀x, P x) → (∀x, C → P x) :=
assume H : C → ∀x, P x,
  take x : T, assume Hc : C,
  H Hc x

theorem thm17b : (∀x, C → P x) → (C → ∀x, P x) :=
assume (H : ∀x, C → P x) (Hc : C),
  take x : T,
  H x Hc

theorem thm18a : ((∃x, P x) → C) → (∀x, P x → C) :=
assume H : (∃x, P x) → C,
  take x, assume Hp : P x,
  have Hex : ∃x, P x, from exists.intro x Hp,
  H Hex

theorem thm18b : (∀x, P x → C) → (∃x, P x) → C :=
assume (H1 : ∀x, P x → C) (H2 : ∃x, P x),
  obtain (w : T) (Hw : P w), from H2,
  H1 w Hw

theorem thm19a : (C ∨ ¬C) → (∃x : T, true) → (C → (∃x, P x)) → (∃x, C → P x) :=
assume (Hem : C ∨ ¬C) (Hin : ∃x : T, true) (H1 : C → ∃x, P x),
  or.elim Hem
    (assume Hc : C,
      obtain (w : T) (Hw : P w), from H1 Hc,
      have Hr : C → P w, from assume Hc, Hw,
      exists.intro w Hr)
    (assume Hnc : ¬C,
      obtain (w : T) (Hw : true), from Hin,
      have Hr : C → P w, from assume Hc, absurd Hc Hnc,
      exists.intro w Hr)

theorem thm19b : (∃x, C → P x) → C → (∃x, P x) :=
assume (H : ∃x, C → P x) (Hc : C),
  obtain (w : T) (Hw : C → P w), from H,
  exists.intro w (Hw Hc)

theorem thm20a : (C ∨ ¬C) → (∃x : T, true) → ((¬∀x, P x) → ∃x, ¬P x) → ((∀x, P x) → C) → (∃x, P x → C) :=
assume Hem Hin Hnf H,
  or.elim Hem
    (assume Hc : C,
      obtain (w : T) (Hw : true), from Hin,
      exists.intro w (assume H : P w, Hc))
    (assume Hnc : ¬C,
      have H1 : ¬(∀x, P x), from mt H Hnc,
      have H2 : ∃x, ¬P x, from Hnf H1,
      obtain (w : T) (Hw : ¬P w), from H2,
      exists.intro w (assume H : P w, absurd H Hw))

theorem thm20b : (∃x, P x → C) → (∀ x, P x) → C :=
assume Hex Hall,
  obtain (w : T) (Hw : P w → C), from Hex,
  Hw (Hall w)

theorem thm21a : (∃x : T, true) → ((∃x, P x) ∨ C) → (∃x, P x ∨ C) :=
assume Hin H,
  or.elim H
    (assume Hex : ∃x, P x,
      obtain (w : T) (Hw : P w), from Hex,
      exists.intro w (or.inl Hw))
    (assume Hc  : C,
      obtain (w : T) (Hw : true), from Hin,
      exists.intro w (or.inr Hc))

theorem thm21b : (∃x, P x ∨ C) → ((∃x, P x) ∨ C) :=
assume H,
  obtain (w : T) (Hw : P w ∨ C), from H,
  or.elim Hw
    (assume H : P w, or.inl (exists.intro w H))
    (assume Hc : C, or.inr Hc)

theorem thm22a : (∀x, P x) ∨ C → ∀x, P x ∨ C :=
assume H, take x,
  or.elim H
    (assume Hl, or.inl (Hl x))
    (assume Hr, or.inr Hr)

theorem thm22b : (C ∨ ¬C) → (∀x, P x ∨ C) → ((∀x, P x) ∨ C) :=
assume Hem H1,
  or.elim Hem
    (assume Hc : C,   or.inr Hc)
    (assume Hnc : ¬C,
      have Hx : ∀x, P x, from
        take x,
        have H1 : P x ∨ C, from H1 x,
        or_resolve_left H1 Hnc,
      or.inl Hx)

theorem thm23a : (∃x, P x) ∧ C → (∃x, P x ∧ C) :=
assume H,
  have Hex : ∃x, P x, from and.elim_left H,
  have Hc : C, from and.elim_right H,
  obtain (w : T) (Hw : P w), from Hex,
  exists.intro w (and.intro Hw Hc)

theorem thm23b : (∃x, P x ∧ C) → (∃x, P x) ∧ C :=
assume H,
  obtain (w : T) (Hw : P w ∧ C), from H,
  have Hex : ∃x, P x, from exists.intro w (and.elim_left Hw),
  and.intro Hex (and.elim_right Hw)

theorem thm24a : (∀x, P x) ∧ C → (∀x, P x ∧ C) :=
assume H, take x,
  and.intro (and.elim_left H x) (and.elim_right H)

theorem thm24b : (∃x : T, true) → (∀x, P x ∧ C) → (∀x, P x) ∧ C :=
assume Hin H,
  obtain (w : T) (Hw : true), from Hin,
  have Hc : C, from and.elim_right (H w),
  have Hx : ∀x, P x, from take x, and.elim_left (H x),
  and.intro Hx Hc

end -- of section
