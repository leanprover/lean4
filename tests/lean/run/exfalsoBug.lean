namespace Ex1

def f (n : Nat) : Option { r : Nat // r ≤ n } :=
  match n with
  | 0   => some ⟨0, Nat.le_refl _⟩
  | n+1 => match f n with
    | some ⟨m, h₁⟩ =>
      have : m < n+1 := Nat.lt_of_le_of_lt h₁ (Nat.lt_succ_self _)
      match f m with
      | some ⟨r, h₂⟩ => some ⟨r, Nat.le_trans h₂ (Nat.le_trans h₁ (Nat.le_succ _))⟩
      | none => none
    | none => none

end Ex1

namespace Ex2

def f (n : Nat) : Option { r : Nat // r ≤ n } :=
  if h : n = 0 then
    some ⟨0, h ▸ Nat.le_refl _⟩
  else
    match f (n-1) with
    | some ⟨m, h₁⟩ =>
      have : m < n := Nat.lt_of_le_of_lt h₁ (Nat.pred_lt h)
      match f m with
      | some ⟨r, h₂⟩ => some ⟨r, Nat.le_trans h₂ (Nat.le_trans h₁ (Nat.pred_le _))⟩
      | none => none
    | none => none

end Ex2

namespace Ex3

def f' (n : Nat) : Option { r : Nat // r ≤ n } :=
  match n with
  | 0   => some ⟨0, Nat.le_refl _⟩
  | n+1 => match f' n with
    | some ⟨m, h₁⟩ =>
      have : m < n+1 := Nat.lt_of_le_of_lt h₁ (Nat.lt_succ_self _)
      match f' m with
      | some ⟨r, h₂⟩ => some ⟨r, Nat.le_trans h₂ (Nat.le_trans h₁ (Nat.le_succ _))⟩
      | none => none
    | none => none

theorem f'_ne_none (n : Nat) : f' n ≠ none := by
  match n with
  | 0   => simp [f']
  | n+1 =>
    simp [f']
    have ih₁ := f'_ne_none n
    split
    next m h₁ he =>
      have : m < n+1 := Nat.lt_of_le_of_lt h₁ (Nat.lt_succ_self _)
      have ih₂ := f'_ne_none m
      split
      next => simp
      next h => contradiction
    next => contradiction

def f (n : Nat) : Option Nat :=
  match f' n with
  | some r => some r.1
  | none => none

theorem f_eq (n : Nat) :
        f n = match n with
          | 0 => some 0
          | n => match f (n - 1) with
            | some m => f m
            | none => none := by
  unfold f
  split
  next r h =>
    revert h
    split <;> try simp [f']
    next => intro h; subst h; simp
    next hne =>
      cases n <;> simp [f']
      next => contradiction
      next n _ =>
       have : Nat.succ n - 1 = n := rfl
       rw [this]
       split <;> try simp
       next r hrn h₁ =>
         split <;> simp
         next => intro he; subst he; simp [*]
  next h_eq_none =>
    have hne := f'_ne_none n
    contradiction

end Ex3
