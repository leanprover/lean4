

def g : List Nat → List Nat → Nat
| [],         y::ys => y
| [],         ys    => 0
| x1::x2::xs, ys    => g xs ys
| x::xs,      y::ys => g xs ys + y
| x::xs,      []    => g xs []

universe u v

inductive Imf {α : Type u} {β : Type v} (f : α → β) : β → Type (max u v)
| mk : (a : α) → Imf f (f a)

def h {α β} {f : α → β} : {b : β} → Imf f b → α
| _, Imf.mk a => a

theorem ex1 {α β} (f : α → β) (a : α) : h (Imf.mk (f := f) a) = a :=
rfl

def v₁ : Imf Nat.succ 1 :=
Imf.mk 0

def v₂ : Imf (fun x => 1 + x) 1 :=
Imf.mk 0

theorem ex2 : h v₁ = 0 :=
rfl

theorem ex3 : h v₂ = 0 :=
rfl

theorem ex4 {α} : {a b : α} → a = b → b = a
| _, _, rfl => rfl

theorem ex5 {α} : {a b : α} → a = b → b = a
| a, .(a), rfl => rfl

theorem ex6 {α} : {a b : α} → a = b → b = a
| a, .(a), Eq.refl .(a) => rfl

theorem ex7 {α} : {a b : α} → a = b → b = a
| .(a), a, Eq.refl .(a) => rfl
