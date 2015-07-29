/-
Example from "Inductively defined types",
from Thierry Coquand and Christine Paulin,
COLOG-88.

It shows it is inconsistent to allow inductive datatypes such as

inductive A : Type :=
| intro : ((A → Prop) → Prop) → A

-/

/- Phi is a positive, but not strictly positive, operator. -/
definition Phi (A : Type) := (A → Prop) → Prop

/- If we were allowed to form the inductive type

     inductive A: Type :=
     | introA : Phi A -> A

   we would get the following
-/

universe l
-- The new type A
axiom A : Type.{l}
-- The constructor
axiom introA : Phi A → A
-- The eliminator
axiom recA   : Π {C : A → Type}, (Π (p : Phi A), C (introA p)) → (Π (a : A), C a)
-- The "computational rule"
axiom recA_comp : Π {C : A → Type} (H : Π (p : Phi A), C (introA p)) (p : Phi A), recA H (introA p) = H p

-- The recursor could be used to define matchA
noncomputable definition matchA (a : A) : Phi A :=
recA (λ p, p) a

-- and the computation rule would allows us to define
lemma betaA (p : Phi A) : matchA (introA p) = p :=
!recA_comp

-- As in all inductive datatypes, we would be able to prove that constructors are injective.
lemma introA_injective : ∀ {p p' : Phi A}, introA p = introA p' → p = p' :=
λ p p' h,
  assert aux : matchA (introA p) = matchA (introA p'), by rewrite h,
  by rewrite [*betaA at aux]; exact aux

-- For any type T, there is an injection from T to (T → Prop)
definition i {T : Type} : T → (T → Prop) :=
λ x y, x = y

lemma i_injective {T : Type} {a b : T} : i a = i b → a = b :=
λ h,
  have e₁ : i a a = i b a,     by rewrite [h],
  have e₂ : (a = a) = (b = a), from e₁,
  have e₃ : b = a,             from eq.subst e₂ rfl,
  eq.symm e₃

-- Hence, by composition, we get an injection f from (A → Prop) to A
noncomputable definition f : (A → Prop) → A :=
λ p, introA (i p)

lemma f_injective : ∀ {p p' : A → Prop}, f p = f p' → p = p':=
λ (p p' : A → Prop) (h : introA (i p) = introA (i p')),
  i_injective (introA_injective h)

/-
  We are now back to the usual Cantor-Russel paradox.
  We can define
-/
noncomputable definition P0 (a : A) : Prop :=
∃ (P : A → Prop), f P = a ∧ ¬ P a
-- i.e., P0 a := codes a set P such that x∉P

noncomputable definition x0 : A := f P0

lemma fP0_eq : f P0 = x0 :=
rfl

lemma not_P0_x0 : ¬ P0 x0 :=
λ h : P0 x0,
  obtain (P : A → Prop) (hp : f P = x0 ∧ ¬ P x0), from h,
  have   fp_eq : f P = f P0,  from and.elim_left hp,
  assert p_eq  : P = P0,      from f_injective fp_eq,
  have   nh    : ¬ P0 x0,     by rewrite [p_eq at hp]; exact (and.elim_right hp),
  absurd h nh

lemma P0_x0 : P0 x0 :=
exists.intro P0 (and.intro fP0_eq not_P0_x0)

theorem inconsistent : false :=
absurd P0_x0 not_P0_x0
