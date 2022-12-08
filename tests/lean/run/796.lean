namespace Ex1
structure A
class B (a : outParam A) (α : Sort u)
class C {a : A} (α : Sort u) [B a α]
class D {a : A} (α : Sort u) [B a α] [c : C α]
class E (a : A) where [c (α : Sort u) [B a α] : C α]
instance c {a : A} [e : E a] (α : Sort u) [B a α] : C α := e.c α

def d {a : A} [E a] (α : Sort u) [B a α] : D α := ⟨⟩
end Ex1

namespace Ex2
class C where f : Sort u → Nat
class D extends C
def a [C] := C.f Nat
def b [D] := D.toC.f Nat
def c [D] := C.f Nat
end Ex2

namespace Ex3
section
variable (N : Type _)
class Zero where
  zero : N
export Zero (zero)
class Succ where
  succ : N → N
export Succ (succ)
class Succ_Not_Zero [Zero N] [Succ N] where
  succ_not_zero {n : N} : succ n ≠ zero
export Succ_Not_Zero (succ_not_zero)
class Eq_Of_Succ_Eq_Succ [Succ N] where
  eq_of_succ_eq_succ {n m : N} (h : succ n = succ m) : n = m
export Eq_Of_Succ_Eq_Succ (eq_of_succ_eq_succ)
class Nat_Induction [Zero N] [Succ N] where
  nat_induction {P : N → Sort _}
    (P0 : P zero)
    (ih : (k : N) → P k → P (succ k))
    (n : N) : P n
export Nat_Induction (nat_induction)
end

section
variable (N : Type _)
class Natural
extends Zero N, Succ N, Succ_Not_Zero N, Eq_Of_Succ_Eq_Succ N, Nat_Induction N
end

section
variable {ℕ} [Natural ℕ]
def pred_with_proof (n : ℕ) (h : n ≠ zero) : Σ' m, n = succ m :=
  by
  revert h
  let P (k : ℕ) := k ≠ zero → Σ' m, k = succ m
  exact (nat_induction (by simp ; exact False.elim) (λ k _ _ => ⟨k, rfl⟩) n : P n)

def pred (n : ℕ) (h : n ≠ zero) : ℕ := (pred_with_proof n h).fst
end
end Ex3
