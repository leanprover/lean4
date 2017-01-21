universe variables u

inductive Vec (α : Type u) : nat → Type (max 1 u)
| nil  : Vec 0
| cons : ∀ {n}, α → Vec n → Vec (nat.succ n)

lemma split {α : Type u} {n : nat} (v : Vec α n) : (v == (Vec.nil α) ∧ n = 0) ∨ ∃ m h (t : Vec α m), v == Vec.cons h t ∧ n = nat.succ m :=
Vec.cases_on v
    (or.inl ⟨heq.refl _, rfl⟩)
    (λ n h t, or.inr ⟨n, h, t, heq.refl _, rfl⟩)

constant f {α : Type u} {n : nat} : Vec α n → nat
axiom fax1 (α : Type u) : f (Vec.nil α) = 0
axiom fax2 {α : Type u} {n : nat} (v : Vec α (nat.succ n)) : f v = 1

example {α : Type u} {n : nat} (v : Vec α n) : f v ≠ 2 :=
begin
  destruct v,
  intros, intro, note h := fax1 α, cc,
  intros n1 h t, intros, intro, note h := fax2 (Vec.cons h t), cc
end

open nat
example : ∀ n, 0 < n → succ (pred n) = n :=
begin
  intro n,
  destruct n,
   {dsimp, intros, note h := lt_irrefl 0, cc},
   {intros, subst n, dsimp, reflexivity}
end
