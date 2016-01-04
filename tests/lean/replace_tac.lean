import data.list
open nat list

example (H : false) : (1 : ℕ) + 1 = (2 : ℕ) :=
begin
  replace (1 : ℕ) with (succ 0) at {1},
end

example (H : false) : (1 : ℕ) + 1 = (2 : ℕ) :=
begin
  replace (1 : ℕ) with (succ 1),
end

definition foo (n : ℕ) : ℕ := n
definition bar := foo
example (h : true) : foo 2 = bar 2 :=
begin
  replace foo 2 with bar 2 at h,
  reflexivity
end

constants (P : ℕ → Type₁) (p : P (3 + 1)) (f : Πn, P n)
example : f (3 + 1) = p :=
begin
  replace ((3 : ℕ) + 1) with (4 : ℕ),
end

variables {A B : Type}
lemma my_map_concat (f : A → B) (a : A) : Πl, map f (concat a l) = concat (f a) (map f l)
| nil    := rfl
| (b::l) := begin
  replace concat a (b :: l) with b :: concat a l,
  replace concat (f a) (map f (b :: l)) with f b :: concat (f a) (map f l),
  replace map f (b :: concat a l) with f b :: map f (concat a l),
  congruence,
  apply my_map_concat

            end
