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
