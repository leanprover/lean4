open nat

inductive {u} Vec (X : Type u) : ℕ → Type u
| nil {} : Vec 0
| cons   : X → Pi {n : nat}, Vec n → Vec (n + 1)

namespace Vec
def get₂ {A : Type} : Π {n : ℕ}, Vec A (succ $ succ n) → A
| n (cons x₁ (cons x₂ xs)) := x₂

def get₂a {A : Type} : Π {n : ℕ}, Vec A (n+2) → A
| 0 (cons x₁ (cons x₂ xs)) := x₂
| (n+1) (cons x₁ (cons x₂ xs)) := x₂

def get₂b {A : Type} : Π {n : ℕ}, Vec A (n+2) → A
| n (cons x₁ (cons x₂ xs)) := x₂

def get₂c {A : Type} : Π {n : ℕ}, Vec A (n+2) → A
| .n (@cons .A x₁ .(n+1) (@cons .A x₂ n xs)) := x₂

def get₂d {A : Type} : Π {n : ℕ}, Vec A (n+2) → A
| .n (@cons .A x₁ (n+1) (@cons .A x₂ .n xs)) := x₂
end Vec
