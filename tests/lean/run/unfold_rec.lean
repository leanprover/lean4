import data.vector
open nat vector

variables {A B : Type}
variable {n : nat}

theorem tst1 : ∀ n m, succ n + succ m = succ (succ (n + m)) :=
begin
  intro n m,
  esimp [add],
  state,
  rewrite [succ_add]
end

definition add2 (x y : nat) : nat :=
nat.rec_on x (λ y, y) (λ x r y, succ (r y)) y

local infix + := add2

theorem tst2 : ∀ n m, succ n + succ m = succ (succ (n + m)) :=
begin
  intro n m,
  esimp [add2],
  state,
  apply sorry
end

definition fib (A : Type) : nat → nat → nat → nat
| b 0      c         := b
| b 1      c         := c
| b (succ (succ a)) c := fib b a c + fib b (succ a) c

theorem fibgt0 : ∀ b n c, fib nat b n c > 0
| b 0 c := sorry
| b 1 c := sorry
| b (succ (succ m)) c :=
begin
  unfold fib,
  state,
  apply sorry
end

theorem unzip_zip : ∀ {n : nat} (v₁ : vector A n) (v₂ : vector B n), unzip (zip v₁ v₂) = (v₁, v₂)
| 0        []      []      := rfl
| (succ m) (a::va) (b::vb) :=
begin
  unfold [zip, unzip],
  state,
  rewrite [unzip_zip]
end
