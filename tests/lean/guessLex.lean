/-!
This files tests Lean's ability to guess the right lexicographic order.

When writing tests for GuesLex, keep in mind that it doesn't do anything
when there is only one plausible measure (one function, only one varying argument).
-/

set_option showInferredTerminationBy true

def ackermann (n m : Nat) := match n, m with
  | 0, m => m + 1
  | .succ n, 0 => ackermann n 1
  | .succ n, .succ m => ackermann n (ackermann (n + 1) m)

def ackermann2 (n m : Nat) := match n, m with
  | m, 0 => m + 1
  | 0, .succ n => ackermann2 1 n
  | .succ m, .succ n => ackermann2 (ackermann2 m (n + 1)) n

def ackermannList (n m : List Unit) := match n, m with
  | [], m => () :: m
  | ()::n, [] => ackermannList n [()]
  | ()::n, ()::m => ackermannList n (ackermannList (()::n) m)

def foo2 : Nat → Nat → Nat
  | .succ n, 1 => foo2 n 1
  | .succ n, 2 => foo2 (.succ n) 1
  | n,       3 => foo2 (.succ n) 2
  | .succ n, 4 => foo2 (if n > 10 then n else .succ n) 3
  | n,       5 => foo2 (n - 1) 4
  | n, .succ m => foo2 n m
  | _, _ => 0

mutual
def even : Nat → Bool
  | 0 => true
  | .succ n => not (odd n)
decreasing_by decreasing_tactic
def odd : Nat → Bool
  | 0 => false
  | .succ n => not (even n)
end

mutual
def evenWithFixed (m : String) : Nat → Bool
  | 0 => true
  | .succ n => not (oddWithFixed m n)
decreasing_by decreasing_tactic
def oddWithFixed (m : String) : Nat → Bool
  | 0 => false
  | .succ n => not (evenWithFixed m n)
end

def ping (n : Nat) := pong n
   where pong : Nat → Nat
  | 0 => 0
  | .succ n => ping n

def hasForbiddenArg (n : Nat) (_h : n = n) (m : Nat) : Nat :=
  match n, m with
  | 0, 0 => 0
  | .succ m, n => hasForbiddenArg m rfl n
  | m, .succ n => hasForbiddenArg (.succ m) rfl n

/-!
Example from “Finding Lexicographic Orders for Termination Proofs in
Isabelle/HOL” by Lukas Bulwahn, Alexander Krauss, and Tobias Nipkow,
10.1007/978-3-540-74591-4_5
-/
def blowup : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | 0, 0, 0, 0, 0, 0, 0, 0 => 0
  | 0, 0, 0, 0, 0, 0, 0, .succ i => .succ (blowup i i i i i i i i)
  | 0, 0, 0, 0, 0, 0, .succ h, i => .succ (blowup h h h h h h h i)
  | 0, 0, 0, 0, 0, .succ g, h, i => .succ (blowup g g g g g g h i)
  | 0, 0, 0, 0, .succ f, g, h, i => .succ (blowup f f f f f g h i)
  | 0, 0, 0, .succ e, f, g, h, i => .succ (blowup e e e e f g h i)
  | 0, 0, .succ d, e, f, g, h, i => .succ (blowup d d d e f g h i)
  | 0, .succ c, d, e, f, g, h, i => .succ (blowup c c d e f g h i)
  | .succ b, c, d, e, f, g, h, i => .succ (blowup b c d e f g h i)

-- Let’s try to confuse the lexicographic guessing function's
-- unpacking of packed n-ary arguments
def confuseLex1 : Nat → @PSigma Nat (fun _ => Nat) → Nat
  | 0, _p => 0
  | .succ n, ⟨x,y⟩ => confuseLex1 n ⟨x, .succ y⟩
decreasing_by decreasing_tactic

def confuseLex2 : @PSigma Nat (fun _ => Nat) → Nat
  | ⟨_,0⟩ => 0
  | ⟨0,_⟩ => 0
  | ⟨.succ y,.succ n⟩ => confuseLex2 ⟨y,n⟩

-- NB: uses sizeOf to make the termination argument non-dependent
def dependent : (n : Nat) → (m : Fin n) → Nat
 | 0, i => Fin.elim0 i
 | .succ 0, 0 => 0
 | .succ (.succ n), 0 => dependent (.succ n) ⟨n, n.lt_succ_self⟩
 | .succ (.succ n), ⟨.succ m, h⟩ =>
  dependent (.succ (.succ n)) ⟨m, Nat.lt_of_le_of_lt (Nat.le_succ _) h⟩

-- NB: does not use sizeOf, as parameters in the fixed prefix are fine.
def dependentWithFixedPrefix (n : Nat) : (m : Fin n) → (acc : Nat) → Nat
  | ⟨0, _⟩, acc => acc
  | ⟨i+1, h⟩, acc => dependentWithFixedPrefix n ⟨i, Nat.lt_of_succ_lt h⟩ (acc + i)

-- An example based on a real world problem, condensed by Leo
inductive Expr where
  | add (a b : Expr)
  | val (n : Nat)

mutual
def eval (a : Expr) : Nat :=
  match a with
  | .add x y => eval_add (x, y)
  | .val n => n

def eval_add (a : Expr × Expr) : Nat :=
  match a with
  | (x, y) => eval x + eval y
end


namespace VarNames

/-! Test that varnames are inferred nicely. -/

def shadow1 (x2 : Nat) : Nat → Nat
  | 0 => 0
  | .succ n => shadow1 (x2 + 1) n
decreasing_by decreasing_tactic


-- This test is a bit moot since #3081, but lets keep it
def some_n : Nat := 1
def shadow2 (some_n : Nat) : Nat → Nat
  | 0 => 0
  | .succ n => shadow2 (some_n + 1) n
decreasing_by decreasing_tactic

-- Tests that the inferred termination argument is shown without extra underscores
def foo : Nat → Nat → Nat → Nat
  | _, 0, acc => acc
  | k, n+1, acc => foo (k+1) n (acc + k)
decreasing_by decreasing_tactic

-- The following test whether `sizeOf` is properly printed, and possibly qualified
-- For this we need a type that needs an explicit “sizeOf”.

structure OddNat where nat : Nat
instance : WellFoundedRelation OddNat := measure (fun ⟨n⟩ => n+1)

-- Just to check that sizeOf is actually used
def oddNat : OddNat → Nat
  | ⟨0⟩ => 0
  | ⟨.succ n⟩ => oddNat ⟨n⟩
decreasing_by decreasing_tactic

-- Shadowing `sizeOf`, as a varying parameter
def shadowSizeOf1 (sizeOf : Nat) : OddNat → Nat
  | ⟨0⟩ => 0
  | ⟨.succ n⟩ => shadowSizeOf1 (sizeOf + 1) ⟨n⟩
decreasing_by decreasing_tactic

-- Shadowing `sizeOf`, as a fixed parameter
def shadowSizeOf2 (sizeOf : Nat) : OddNat → Nat → Nat
  | ⟨0⟩, m => m
  | ⟨.succ n⟩, m => shadowSizeOf2 sizeOf ⟨n⟩ m
decreasing_by decreasing_tactic

-- Shadowing `sizeOf`, as something in the environment
def sizeOf : Nat := 2

def qualifiedSizeOf (m : Nat) : OddNat → Nat
  | ⟨0⟩ => 0
  | ⟨.succ n⟩ => qualifiedSizeOf (m + 1) ⟨n⟩
decreasing_by decreasing_tactic

end VarNames


namespace MutualNotNat1

-- A type that isn't Nat, checking that the inferred argument uses `sizeOf` so that
-- the types of the termination argument aligns.
structure OddNat2 where nat : Nat
instance : SizeOf OddNat2 := ⟨fun n => n.nat⟩
@[simp] theorem  OddNat2.sizeOf_eq (n : OddNat2) : sizeOf n = n.nat := rfl
mutual
def foo : Nat → Nat
  | 0 => 0
  | n+1 => bar ⟨n⟩
def bar : OddNat2 → Nat
  | ⟨0⟩ => 0
  | ⟨n+1⟩ => foo n
end
end MutualNotNat1

namespace MutualNotNat2
-- A type that is defeq to Nat, but with a different `sizeOf`, checking that the
-- inferred argument uses `sizeOf` so that the types of the termination argument aligns.
def OddNat3 := Nat
instance : SizeOf OddNat3 := ⟨fun n => 42 - @id Nat n⟩
@[simp] theorem  OddNat3.sizeOf_eq (n : OddNat3) : sizeOf n = 42 - @id Nat n := rfl
mutual
def foo : Nat → Nat
  | 0 => 0
  | n+1 =>
    if h : n < 42 then bar (42 - n) else 0
  -- termination_by x1 => x1
  decreasing_by simp; omega
def bar (o : OddNat3) : Nat := if h : @id Nat o < 41 then foo (41 - @id Nat o) else 0
  -- termination_by sizeOf o
  decreasing_by simp [id] at *; omega
end
end MutualNotNat2

namespace MutualNotNat3
-- A variant of the above, but where the type of the parameter refined to `Nat`.
-- Previously `GuessLex` was inferring the `SizeOf` instance based on the type of the
-- *concrete* parameter or argument, which was wrong.
-- The inference needs to be based on the parameter type in the function's signature.
def OddNat3 := Nat
instance : SizeOf OddNat3 := ⟨fun n => 42 - @id Nat n⟩
@[simp] theorem  OddNat3.sizeOf_eq (n : OddNat3) : sizeOf n = 42 - @id Nat n := rfl
mutual
def foo : Nat → Nat
  | 0 => 0
  | n+1 =>
    if h : n < 42 then bar (42 - n) else 0
  -- termination_by x1 => x1
  decreasing_by simp; omega
def bar : OddNat3 → Nat
  | Nat.zero => 0
  | n+1 => if h : n < 41 then foo (40 - n) else 0
  -- termination_by x1 => sizeOf x1
  decreasing_by simp; omega
end
end MutualNotNat3
