example (a b : nat) : (λ x, a + x) 0 = b + 1 + a :=
begin
  conv in (_ + 1) { change nat.succ b },
  guard_target (λ x, a + x) 0 = nat.succ b + a,
  admit
end

def Div : nat → nat → nat | x y :=
if h : 0 < y ∧ y ≤ x
then
  have x - y < x, from sorry,
  Div (x - y) y + 1
else 0

example (x y : nat) : 0 < y → y ≤ x → Div x y = Div (x - y) y + 1 :=
begin
  intros h1 h2,
  -- Use conv to focus on the lhs
  conv { to_lhs, simp [Div] {single_pass := tt}, simp [h1, h2] },
  guard_target 1 + Div (x - y) y = Div (x - y) y + 1,
  simp
end

example (x y : nat) (f : nat → nat) (h : f (0 + x + y) = 0 + y) : f (x + y) = 0 + y :=
begin
  -- use conv to rewrite subterm of a hypothesis
  conv at h in (0 + _) { simp },
  assumption
end

example (x y : nat) (f : nat → nat) (h : f (0 + x + y) = 0 + y) : f (x + y) = 0 + y :=
begin
  -- use conv to rewrite subterm of a hypothesis
  conv at h in (0 + x) { simp },
  assumption
end

example (x y : nat) (f : nat → nat) (h : f (0 + x + y) = 0 + y) : f (x + y) = 0 + y :=
begin
  -- use congr primitive to find term to be modified
  conv at h {
    guard_lhs f (0 + x + y) = 0 + y,
    congr,
    { guard_lhs f (0 + x + y),
      congr, congr, simp },
    { guard_lhs 0 + y }
  },
  assumption
end

example (x y : nat) (f : nat → nat) (h : f (0 + x + y) = 0 + y) : f (x + y) = 0 + y :=
begin
  -- use congr primitive to find term to be modified
  conv at h {
    guard_lhs f (0 + x + y) = 0 + y,
    to_lhs,
    guard_lhs f (0 + x + y),
    congr,
    guard_lhs 0 + x + y,
    congr,
    simp,
  },
  assumption
end

example (x y : nat) (f : nat → nat) (h : f (0 + x + y) = 0 + y) : f (x + y) = 0 + y :=
begin
  -- use conv to rewrite subterm of a hypothesis
  conv at h in (0 + _) { rw [zero_add] },
  assumption
end

example (x y : nat) (f : nat → nat) (h : f (0 + x + y) = 0 + y) : f (0 + x + y) = y :=
begin
  -- use conv to rewrite rhs a hypothesis
  conv at h { to_rhs, rw [zero_add] },
  assumption
end

example (x : nat) (f : nat → nat) (h₁ : x = 0) (h₂ : ∀ x, f x = x + x) : f x = x :=
begin
  conv { to_rhs, rw [h₁, -add_zero 0, -h₁], },
  exact h₂ x
end

lemma addz (x : nat) : x + 0 = x :=
rfl

example (x : nat) (g : nat → nat) (f : nat → (nat → nat) → nat) (h : f (x + 0) (λ x, g x) = x) : f x g = x :=
begin
  conv at h {dsimp [addz] {eta := ff}},
  conv at h {dsimp},
  exact h,
end

example (x : nat) (g : nat → nat) (f : nat → (nat → nat) → nat) (h : f (x + 0) (λ x, g x) = x) : f x g = x :=
begin
  conv at h {dsimp [addz] {eta := ff},
             guard_lhs f x (λ x, g x) = x,
             dsimp,
             guard_lhs f x g = x},
  exact h,
end

def f (x y : nat) : nat :=
x + y + 1

example (x y : nat) : f x y + f x x + f y y = x + y + 1 + y + y + 1 + f x x :=
begin
  conv {
    -- execute `rw [f]` for 1st and 3rd occurrences of f-applications
    for (f _ _) [1, 3] { rw [f] },
    guard_lhs (x + y + 1) + f x x + (y + y + 1) = x + y + 1 + y + y + 1 + f x x,
    simp
  }
end

example (x : nat) : f x x + f x x + f x x = f x x + x + x + x + x + 1 + 1 :=
begin
  conv {
    -- execute `rw [f]` for 1st and 3rd occurrences of f-applications
    for (f _ _) [1, 3] { rw [f] },
    guard_lhs (x + x + 1) + f x x + (x + x + 1) = f x x + x + x + x + x + 1 + 1,
    simp
  }
end

example (x : nat) : f x x + f x x = f x x + x + x + 1 :=
begin
  conv in (f _ _) { rw [f] },
  guard_target (x + x + 1) + f x x = f x x + x + x + 1,
  simp
end
