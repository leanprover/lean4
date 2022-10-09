namespace MWE

inductive Id {A : Type u} : A → A → Type u
| refl {a : A} : Id a a

attribute [eliminator] Id.casesOn

infix:50 (priority := high) " = " => Id

def symm {A : Type u} {a b : A} (p : a = b) : b = a :=
by { induction p; exact Id.refl }

def map {A : Type u} {B : Type v} {a b : A} (f : A → B) (p : a = b) : f a = f b :=
by { induction p; apply Id.refl }

def transport {A : Type u} (B : A → Type v) {a b : A} (p : a = b) : B a → B b :=
by { induction p; exact id }

def boolToUniverse : Bool → Type
| true  => Unit
| false => Empty

def ffNeqTt : false = true → Empty :=
λ p => transport boolToUniverse (symm p) ()

def isZero : Nat → Bool
| Nat.zero   => true
| Nat.succ _ => false

set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option trace.Compiler.result true
def succNeqZero (n : Nat) : Nat.succ n = 0 → Empty :=
λ h => ffNeqTt (map isZero h)
