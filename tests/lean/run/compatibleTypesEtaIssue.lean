namespace MWE

universe u v w

inductive Id {A : Type u} : A → A → Type u
| refl {a : A} : Id a a

infix:50 (priority := high) " = " => Id

def contr (A : Type u) := Σ (a : A), ∀ b, a = b

def singl {A : Type u} (a : A) :=
Σ b, a = b

def Corr (A : Type u) (B : Type v) :=
Σ (R : A → B → Type w), (∀ a, contr (Σ b, R a b)) × (∀ b, contr (Σ a, R a b))

def Homotopy {A : Type u} {B : A → Type v} (f g : ∀ x, B x) :=
∀ (x : A), f x = g x
infix:80 " ~ " => Homotopy

def isQinv {A : Type u} {B : Type v} (f : A → B) (g : B → A) :=
(f ∘ g ~ id) × (g ∘ f ~ id)

def Qinv {A : Type u} {B : Type v} (f : A → B) :=
Σ (g : B → A), isQinv f g

def Qinv.eqv (A : Type u) (B : Type v) :=
Σ (f : A → B), Qinv f

def linv {A : Type u} {B : Type v} (f : A → B) :=
Σ (g : B → A), g ∘ f ~ id

def rinv {A : Type u} {B : Type v} (f : A → B) :=
Σ (g : B → A), f ∘ g ~ id

def biinv {A : Type u} {B : Type v} (f : A → B) :=
linv f × rinv f

def Equiv (A : Type u) (B : Type v) : Type (max u v) :=
Σ (f : A → B), biinv f
infix:25 " ≃ " => Equiv

def ax₁ {A : Type u} {B : Type v} : A ≃ B → contr A → contr B :=
  sorry
def ax₂ {A : Type v} {B : Type u} (f g : A → B) : (Σ x, f x = g x) ≃ (Σ x, g x = f x) :=
  sorry
def ax₄ {A : Type u} {B : Type v} (w : Qinv.eqv A B) (b : B) : contr (Σ a, b = w.1 a) :=
  sorry
def ax₃ {A : Type u} (a : A) : contr (singl a) :=
  sorry

def corrOfQinv {A : Type u} {B : Type v} : Qinv.eqv A B → Corr A B :=
by { intro w; exists (λ a b => b = w.1 a); apply Prod.mk <;> intro x;
     apply ax₁; apply ax₂; apply ax₃; apply ax₄ }
