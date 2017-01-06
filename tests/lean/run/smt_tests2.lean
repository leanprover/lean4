example (a b c : nat) (f : nat → nat → nat) : f 0 1 = 1 → (λ x y : nat, x) = f → false :=
begin [smt]
  close
end

example (a b c : nat) (f : nat → nat → nat) : f 0 1 = 1 → f = (λ x y, x) → false :=
begin [smt]
  close
end

example (a b c : nat) (f : nat → nat) : f = (λ x, x) → f 0 = 1 → false :=
begin [smt]
  close
end

example (a b c : nat) (f : nat → nat) : (λ x : nat, x) = f → f 0 = 1 → false :=
begin [smt]
  close
end

open list
universe variables u

example {α : Type u} (l : list α) (a : α) (f : α → α × α) :
        f = (λ x, (x, x)) → map f (a::l) = (a, a) :: map f l :=
begin [smt]
  add_eqn_lemmas map,
  ematch
end

example {α : Type u} (l : list α) (a : α) (f : α → α × α) :
        map f (a::l) ≠ (a, a) :: map f l → f = (λ x, (x, x)) → false :=
begin [smt]
  add_eqn_lemmas map,
  ematch
end

example (a b c : nat) (f : nat → nat → nat) : f 0 1 = 1 → (λ (x : nat) (y : char), x) == f → f = (λ (x : nat) (y : nat), 2) → false :=
begin [smt]
  close
end

/-
The following kind of propagation is not supported yet.
We can add it if it is needed in practice.

example (a b c : nat) (f : nat → nat → nat) : (λ x : nat, x) = f b → f b 0 = 1 → false :=
begin [smt]
  close
end
-/
