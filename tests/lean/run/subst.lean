#lang lean4

universes u

def f1 (n m : Nat) (x : Fin n) (h : n = m) : Fin m :=
h ▸ x

def f2 (n m : Nat) (x : Fin n) (h : m = n) : Fin m :=
h ▸ x

theorem ex1 {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c :=
h₂ ▸ h₁

theorem ex2 {α : Sort u} {a b : α} (h : a = b) : b = a :=
h ▸ rfl

theorem ex3 {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) : r a c :=
h₂ ▸ h₁

theorem ex4 {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : a = b) (h₂ : r b c) : r a c :=
h₁ ▸ h₂

theorem ex5 {p : Prop} (h : p = True) : p :=
h ▸ trivial

theorem ex6 {p : Prop} (h : p = False) : ¬p :=
fun hp => h ▸ hp

theorem ex7 {α} {a b c d : α} (h₁ : a = c) (h₂ : b = d) (h₃ : c ≠ d) : a ≠ b :=
h₁ ▸ h₂ ▸ h₃

theorem ex8 (n m k : Nat) (h : Nat.succ n + m = Nat.succ n + k) : Nat.succ (n + m) = Nat.succ (n + k) :=
Nat.succAdd .. ▸ Nat.succAdd .. ▸ h

theorem ex9 (a b : Nat) (h₁ : a = a + b) (h₂ : a = b) : a = b + a  :=
h₂ ▸ h₁

theorem ex10 (a b : Nat) (h : a = b) : b = a :=
h ▸ rfl
