namespace Ex1

inductive Wk: Nat -> Nat -> Type 0 where
  | id: Wk n n
  | step: Wk m n -> Wk (Nat.succ m) n
  | lift: Wk m n -> Wk (Nat.succ m) (Nat.succ n)

def wk_comp {n m l: Nat} (ρ: Wk n m) (σ: Wk m l): Wk n l :=
  match n, m, l, ρ, σ with
    | _, _, _, Wk.id, σ => σ
    | _, _, _, Wk.step ρ, σ => Wk.step (wk_comp ρ σ)
    | _, _, _, Wk.lift ρ, Wk.id => Wk.lift ρ
    | _, _, _, Wk.lift ρ, Wk.step σ => Wk.step (wk_comp ρ σ)
    | _, _, _, Wk.lift ρ, Wk.lift σ => Wk.lift (wk_comp ρ σ)

theorem wk_comp_id_id {ρ: Wk m n}: wk_comp Wk.id ρ = ρ := rfl

end Ex1


namespace Ex2

inductive Wk: Nat -> Nat -> Type 0 where
  | id: Wk n n
  | step: Wk m n -> Wk (Nat.succ m) n

def wk_comp : Wk n m → Wk m l → Wk n l
  | Wk.id, σ => σ
  | Wk.step ρ, σ => Wk.step (wk_comp ρ σ)

theorem wk_comp_id_id {ρ: Wk m n}: wk_comp Wk.id ρ = ρ := rfl

end Ex2
