/-!
Tests the type of the function packing a `mutual` block defined by well-founded recursion: case
splits on the packed argument are only used where the result types of the functions differ.
-/

namespace Same

mutual
def f₁ : Nat → Nat
  | 0 => 0
  | n + 1 => f₂ n
termination_by n => n
def f₂ : Nat → Nat
  | 0 => 0
  | n + 1 => f₃ n
termination_by n => n
def f₃ : Nat → Nat
  | 0 => 0
  | n + 1 => f₄ n
termination_by n => n
def f₄ : Nat → Nat
  | 0 => 0
  | n + 1 => f₁ n
termination_by n => n
end

/-- info: Same.f₁._mutual : (Nat ⊕' Nat) ⊕' Nat ⊕' Nat → Nat -/
#guard_msgs in
#check f₁._mutual

end Same

namespace Mixed

mutual
def f₁ : Nat → Nat
  | 0 => 0
  | n + 1 => f₂ n
termination_by n => n
def f₂ : Nat → Nat
  | 0 => 0
  | n + 1 => if f₃ n then 1 else 0
termination_by n => n
def f₃ : Nat → Bool
  | 0 => true
  | n + 1 => f₄ n
termination_by n => n
def f₄ : Nat → Bool
  | 0 => false
  | n + 1 => f₁ n == 0
termination_by n => n
end

/--
info: Mixed.f₁._mutual (x✝ : (Nat ⊕' Nat) ⊕' Nat ⊕' Nat) : PSum.casesOn x✝ (fun _x => Nat) fun _x => Bool
-/
#guard_msgs in
#check f₁._mutual

end Mixed

namespace Dependent

mutual
def f₁ : (n : Nat) → Fin (n + 1)
  | 0 => 0
  | n + 1 => (f₂ n).castSucc
termination_by n => n
def f₂ : (n : Nat) → Fin (n + 1)
  | 0 => 0
  | n + 1 => if f₃ n = 0 then (f₁ n).castSucc else 0
termination_by n => n
def f₃ : Nat → Nat
  | 0 => 0
  | n + 1 => f₃ n + (f₁ n).val
termination_by n => n
end

/--
info: Dependent.f₁._mutual (x✝ : Nat ⊕' Nat ⊕' Nat) :
  PSum.casesOn x✝ (fun _x => Fin (_x + 1)) fun _x => PSum.casesOn _x (fun _x => Fin (_x + 1)) fun _x => Nat
-/
#guard_msgs in
#check f₁._mutual

end Dependent
