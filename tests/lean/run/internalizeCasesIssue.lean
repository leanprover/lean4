namespace MWE

inductive Id {A : Type u} : A → A → Type u
| refl {a : A} : Id a a

attribute [induction_eliminator] Id.casesOn

infix:50 (priority := high) " = " => Id

def symm {A : Type u} {a b : A} (p : a = b) : b = a :=
by { induction p; exact Id.refl }

def transport {A : Type u} (B : A → Type v) {a b : A} (p : a = b) : B a → B b :=
by { induction p; exact id }

def transportconst {A B : Type u} : A = B → A → B :=
transport id

def transportconstInv {A B : Type u} (e : A = B) : B → A :=
transportconst (symm e)

def transportconstOverInv {A B : Type u} (p : A = B) :
  ∀ x, transportconst (symm p) x = transportconstInv p x :=
by { intro x; apply Id.refl }

def transportconstInv' {A B : Type u} : A = B → B → A :=
  transportconst ∘ symm
