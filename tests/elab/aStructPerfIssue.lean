set_option warn.classDefReducibility false

noncomputable section
namespace MWE

universe u v w

inductive Id {A : Type u} : A → A → Type u
| refl {a : A} : Id a a

attribute [cases_eliminator] Id.casesOn

infix:50 (priority := high) " = " => Id

@[match_pattern] abbrev idp {A : Type u} (a : A) : a = a := Id.refl

def Id.symm {A : Type u} {a b : A} (p : a = b) : b = a :=
by { induction p; apply idp }

def Id.map {A : Type u} {B : Type v} {a b : A} (f : A → B) (p : a = b) : f a = f b :=
by { induction p; apply idp }

def Id.trans {A : Type u} {a b c : A} (p : a = b) (q : b = c) : a = c :=
by { induction p; apply q }

infixl:60 " ⬝ " => Id.trans
postfix:max "⁻¹" => Id.symm

def Id.reflRight {A : Type u} {a b : A} (p : a = b) : p ⬝ idp b = p :=
by { induction p; apply idp }

def Iff (A : Type u) (B : Type v) :=
(A → B) × (B → A)

infix:30 (priority := high) " ↔ " => Iff

def Iff.left  {A : Type u} {B : Type v} (w : A ↔ B) : A → B := w.1
def Iff.right {A : Type u} {B : Type v} (w : A ↔ B) : B → A := w.2

def Iff.comp {A : Type u} {B : Type v} {C : Type w} :
  (A ↔ B) → (B ↔ C) → (A ↔ C) :=
λ p q => (q.left ∘ p.left, p.right ∘ q.right)

inductive Empty : Type u
attribute [cases_eliminator] Empty.casesOn

notation "𝟎" => Empty

def Not (A : Type u) : Type u := A → (𝟎 : Type)
def Neq {A : Type u} (a b : A) := Not (Id a b)

prefix:90 (priority := high) "¬" => Not
infix:50 (priority := high) " ≠ " => Neq

def dec (A : Type u) := Sum A (¬A)

inductive hlevel
| minusTwo
| succ : hlevel → hlevel

notation "ℕ₋₂" => hlevel
notation "−2" => hlevel.minusTwo
notation "−1" => hlevel.succ hlevel.minusTwo

def hlevel.ofNat : Nat → ℕ₋₂
| Nat.zero   => succ (succ −2)
| Nat.succ n => hlevel.succ (ofNat n)

instance (n : Nat) : OfNat ℕ₋₂ n := ⟨hlevel.ofNat n⟩

def contr (A : Type u) := Σ (a : A), ∀ b, a = b

def prop (A : Type u) := ∀ (a b : A), a = b
def hset (A : Type u) := ∀ (a b : A) (p q : a = b), p = q

def propset := Σ (A : Type u), prop A
notation "Ω" => propset

def isNType : hlevel → Type u → Type u
| −2            => contr
| hlevel.succ n => λ A => ∀ (x y : A), isNType n (x = y)

notation "is-" n "-type" => isNType n

def nType (n : hlevel) : Type (u + 1) :=
Σ (A : Type u), is-n-type A

notation n "-Type" => nType n

inductive Unit : Type u
| star : Unit

attribute [cases_eliminator] Unit.casesOn

def Homotopy {A : Type u} {B : A → Type v} (f g : ∀ x, B x) :=
∀ (x : A), f x = g x
infix:80 " ~ " => Homotopy

def linv {A : Type u} {B : Type v} (f : A → B) :=
Σ (g : B → A), g ∘ f ~ id

def rinv {A : Type u} {B : Type v} (f : A → B) :=
Σ (g : B → A), f ∘ g ~ id

def biinv {A : Type u} {B : Type v} (f : A → B) :=
linv f × rinv f

def Equiv (A : Type u) (B : Type v) : Type (max u v) :=
Σ (f : A → B), biinv f
infix:25 " ≃ " => Equiv

namespace Equiv
  def forward {A : Type u} {B : Type v} (e : A ≃ B) : A → B := e.fst

  def left {A : Type u} {B : Type v} (e : A ≃ B) : B → A := e.2.1.1
  def right {A : Type u} {B : Type v} (e : A ≃ B) : B → A := e.2.2.1

  def leftForward {A : Type u} {B : Type v} (e : A ≃ B) : e.left ∘ e.forward ~ id := e.2.1.2
  def forwardRight {A : Type u} {B : Type v} (e : A ≃ B) : e.forward ∘ e.right ~ id := e.2.2.2

  def biinvTrans {A : Type u} {B : Type v} {C : Type w}
    {f : A → B} {g : B → C} (e₁ : biinv f) (e₂ : biinv g) : biinv (g ∘ f) :=
  (⟨e₁.1.1 ∘ e₂.1.1, λ x => Id.map e₁.1.1 (e₂.1.2 (f x)) ⬝ e₁.1.2 x⟩,
   ⟨e₁.2.1 ∘ e₂.2.1, λ x => Id.map g (e₁.2.2 (e₂.2.1 x)) ⬝ e₂.2.2 x⟩)

  def trans {A : Type u} {B : Type v} {C : Type w}
    (f : A ≃ B) (g : B ≃ C) : A ≃ C :=
  ⟨g.1 ∘ f.1, biinvTrans f.2 g.2⟩

  def ideqv (A : Type u) : A ≃ A :=
  ⟨id, (⟨id, idp⟩, ⟨id, idp⟩)⟩
end Equiv

def transport {A : Type u} (B : A → Type v) {a b : A} (p : a = b) : B a → B b :=
by { induction p; apply id }

def subst {A : Type u} {B : A → Type v} {a b : A} (p : a = b) : B a → B b :=
transport B p

def transportComposition {A : Type u} {a x₁ x₂ : A}
  (p : x₁ = x₂) (q : a = x₁) : transport (Id a) p q = q ⬝ p :=
by { induction p; apply Id.symm; apply Id.reflRight }

def rewriteComp {A : Type u} {a b c : A}
  {p : a = b} {q : b = c} {r : a = c} (h : r = p ⬝ q) : p⁻¹ ⬝ r = q :=
by { induction p; apply h }

def invComp {A : Type u} {a b : A} (p : a = b) : p⁻¹ ⬝ p = idp b :=
by { induction p; apply idp }

def apd {A : Type u} {B : A → Type v} {a b : A}
  (f : ∀ (x : A), B x) (p : a = b) : subst p (f a) = f b :=
by { induction p; apply idp }

def propEquivLemma {A : Type u} {B : Type v}
  (F : prop A) (G : prop B) (f : A → B) (g : B → A) : A ≃ B :=
⟨f, (⟨g, λ _ => F _ _⟩, ⟨g, λ _ => G _ _⟩)⟩

axiom funext {A : Type u} {B : A → Type v} {f g : ∀ x, B x} (p : f ~ g) : f = g

def propIsSet {A : Type u} (r : prop A) : hset A :=
by {
  intro x y p q; have g := r x; apply Id.trans;
  apply Id.symm; apply rewriteComp;
  exact (apd g p)⁻¹ ⬝ transportComposition p (g x);
  induction q; apply invComp
}

def contrImplProp {A : Type u} (h : contr A) : prop A :=
λ a b => (h.2 a)⁻¹ ⬝ (h.2 b)

def contrIsProp {A : Type u} : prop (contr A) :=
by {
  intro ⟨x, u⟩ ⟨y, v⟩; have p := u y;
  induction p; apply Id.map;
  apply funext; intro a;
  apply propIsSet (contrImplProp ⟨x, u⟩)
}

def ntypeIsProp : ∀ (n : hlevel) {A : Type u}, prop (is-n-type A)
| −2            => contrIsProp
| hlevel.succ n => λ p q => funext (λ x => funext (λ y => ntypeIsProp n _ _))

def propIsProp {A : Type u} : prop (prop A) :=
by {
  intro f g;
  apply funext; intro;
  apply funext; intro;
  apply propIsSet; assumption
}

def minusOneEqvProp {A : Type u} : (is-(−1)-type A) ≃ prop A :=
by {
  apply propEquivLemma; apply ntypeIsProp; apply propIsProp;
  { intro H a b; exact (H a b).1 };
  { intro H a b; exists H a b; apply propIsSet H }
}

def equivFunext {A : Type u} {η μ : A → Type v}
  (H : ∀ x, η x ≃ μ x) : (∀ x, η x) ≃ (∀ x, μ x) :=
by {
  exists (λ (f : ∀ x, η x) (x : A) => (H x).forward (f x)); apply Prod.mk;
  { exists (λ (f : ∀ x, μ x) (x : A) => (H x).left (f x));
    intro f; apply funext;
    intro x; apply (H x).leftForward };
  { exists (λ (f : ∀ x, μ x) (x : A) => (H x).right (f x));
    intro f; apply funext;
    intro x; apply (H x).forwardRight }
}

def zeroEqvSet {A : Type u} : (is-0-type A) ≃ hset A :=
Equiv.trans (Equiv.trans (Equiv.ideqv _) (equivFunext (λ x => equivFunext (λ y => minusOneEqvProp)))) (Equiv.ideqv _)

notation "𝟏" => Unit
notation "★" => Unit.star

def vect (A : Type u) : Nat → Type u
| Nat.zero   => 𝟏
| Nat.succ n => A × vect A n

def algop (deg : Nat) (A : Type u) :=
vect A deg → A

def algrel (deg : Nat) (A : Type u) :=
vect A deg → Ω

def zeroeqv {A : Type u} (H : hset A) : 0-Type :=
⟨A, zeroEqvSet.left H⟩

section
  variable {ι : Type u} {υ : Type v} (deg : Sum ι υ → Nat)

  def Algebra (A : Type w) :=
  (∀ i, algop  (deg (Sum.inl i)) A) ×
  (∀ i, algrel (deg (Sum.inr i)) A)

  def Alg := Σ (A : 0-Type), Algebra deg A.1
end

section
  variable {ι : Type u} {υ : Type v} {deg : Sum ι υ → Nat} (A : Alg deg)
  def Alg.carrier := A.1.1
  def Alg.op      := A.2.1
  def Alg.rel     := A.2.2

  def Alg.hset : hset A.carrier :=
  zeroEqvSet.forward A.1.2
end

namespace Precategory
  inductive Arity : Type
  | left | right | mul | bottom

  def signature : Sum Arity 𝟎 → Nat
  | Sum.inl Arity.mul     => 2
  | Sum.inl Arity.left    => 1
  | Sum.inl Arity.right   => 1
  | Sum.inl Arity.bottom  => 0
end Precategory

def Precategory : Type (u + 1) :=
Alg.{0, 0, u, 0} Precategory.signature

namespace Precategory
  variable (𝒞 : Precategory.{u})

  def intro {α : Type u} (H : hset α) (μ : α → α → α)
    (dom cod : α → α) (bot : α) : Precategory.{u} :=
  ⟨zeroeqv H,
   (λ | Arity.mul     => λ (a, b, _) => μ a b
      | Arity.left    => λ (a, _) => dom a
      | Arity.right   => λ (a, _) => cod a
      | Arity.bottom  => λ _ => bot,
    λ z => nomatch z)⟩

  def carrier := 𝒞.1.1

  def bottom : 𝒞.carrier :=
  𝒞.op Arity.bottom ★
  notation "∄" => bottom _

  def μ : 𝒞.carrier → 𝒞.carrier → 𝒞.carrier :=
  λ x y => 𝒞.op Arity.mul (x, y, ★)

  def dom : 𝒞.carrier → 𝒞.carrier :=
  λ x => 𝒞.op Arity.left (x, ★)

  def cod : 𝒞.carrier → 𝒞.carrier :=
  λ x => 𝒞.op Arity.right (x, ★)

  def following (a b : 𝒞.carrier) :=
  𝒞.dom a = 𝒞.cod b

  def defined (x : 𝒞.carrier) := x ≠ ∄
  prefix:70 "∃" => defined _
end Precategory

class category (𝒞 : Precategory) :=
(defDec      : ∀ (a : 𝒞.carrier), dec (a = ∄))
(bottomLeft  : ∀ a, 𝒞.μ ∄ a = ∄)
(bottomRight : ∀ a, 𝒞.μ a ∄ = ∄)
(bottomDom   : 𝒞.dom ∄ = ∄)
(bottomCod   : 𝒞.cod ∄ = ∄)
(domComp     : ∀ a, 𝒞.μ a (𝒞.dom a) = a)
(codComp     : ∀ a, 𝒞.μ (𝒞.cod a) a = a)
(mulDom      : ∀ a b, ∃(𝒞.μ a b) → 𝒞.dom (𝒞.μ a b) = 𝒞.dom b)
(mulCod      : ∀ a b, ∃(𝒞.μ a b) → 𝒞.cod (𝒞.μ a b) = 𝒞.cod a)
(domCod      : 𝒞.dom ∘ 𝒞.cod ~ 𝒞.cod)
(codDom      : 𝒞.cod ∘ 𝒞.dom ~ 𝒞.dom)
(mulAssoc    : ∀ a b c, 𝒞.μ (𝒞.μ a b) c = 𝒞.μ a (𝒞.μ b c))
(mulDef      : ∀ a b, ∃a → ∃b → (∃(𝒞.μ a b) ↔ 𝒞.following a b))
open category

def op (𝒞 : Precategory) : Precategory :=
Precategory.intro 𝒞.hset (λ a b => 𝒞.μ b a) 𝒞.cod 𝒞.dom ∄

postfix:max "ᵒᵖ" => op
set_option maxHeartbeats 400000
def dual (𝒞 : Precategory) (η : category 𝒞) : category 𝒞ᵒᵖ :=
{ defDec      := @defDec 𝒞 η,
  bottomLeft  := @bottomRight 𝒞 η,
  bottomRight := @bottomLeft 𝒞 η,
  bottomDom   := @bottomCod 𝒞 η,
  bottomCod   := @bottomDom 𝒞 η,
  domComp     := @codComp 𝒞 η,
  codComp     := @domComp 𝒞 η,
  mulDom      := λ _ _ δ => @mulCod 𝒞 η _ _ δ,
  mulCod      := λ _ _ δ => @mulDom 𝒞 η _ _ δ,
  domCod      := @codDom 𝒞 η,
  codDom      := @domCod 𝒞 η,
  mulAssoc    := λ _ _ _ => Id.symm (@mulAssoc 𝒞 η _ _ _),
  mulDef      := λ a b α β => Iff.comp (@mulDef 𝒞 η b a β α) (Id.symm, Id.symm)
}

end MWE
end
