import data.nat
open algebra

constant f {A : Type} : A → A → A

theorem test1 {A : Type} [s : comm_ring A] (a b c : A) : f (a + 0) (f (a + 0) (a + 0)) = f a (f (0 + a) a) :=
begin
  rewrite [add_zero at {1, 3}, -- rewrite 1st and 3rd occurrences
           {0 + _}add.comm]   -- apply commutativity to (0 + _)
end

check @mul_zero

axiom Ax {A : Type} [s₁ : has_mul A] [s₂ : has_zero A] (a : A) : f (a * 0) (a * 0) = 0

theorem test2 {A : Type} [s : comm_ring A] (a b c : A) : f 0 0 = 0 :=
begin
  rewrite [
    -(mul_zero a) at {1, 2},  -- - means apply symmetry, rewrite 0 ==> a * 0  at 1st and 2nd occurrences
    Ax]                      -- use Ax as rewrite rule
end

theorem test3 {A : Type} [s : comm_ring A] (a b c : A) : a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
begin
  rewrite [+mul_zero, +zero_mul, +add_zero] -- in rewrite rules, + is notation for one or more
end

reveal test3
print definition test3

theorem test4 {A : Type} [s : comm_ring A] (a b c : A) : a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
begin
  rewrite [*mul_zero, *zero_mul, *add_zero, *zero_add] -- in rewrite rules, * is notation for zero or more
end

theorem test5 {A : Type} [s : comm_ring A] (a b c : A) : a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
begin
  rewrite [
    2 mul_zero,   -- apply mul_zero exactly twice
    2 zero_mul,  -- apply zero_mul exactly twice
    5>add_zero]   -- apply add_zero at most 5 times
end
