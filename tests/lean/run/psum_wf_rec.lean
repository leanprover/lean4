def psum.alt.sizeof {α β} [has_sizeof α] [has_sizeof β] : psum α β → nat
| (psum.inl a) := 2*sizeof a + 2
| (psum.inr b) := 2*sizeof b + 1

def sum_has_sizeof_2 {α β} [has_sizeof α] [has_sizeof β] : has_sizeof (psum α β) :=
⟨psum.alt.sizeof⟩

local attribute [instance] sum_has_sizeof_2
local attribute [simp] add_comm add_left_comm add_assoc mul_assoc mul_comm mul_left_comm

mutual def f, g
with f : ℕ → ℕ
| n := g n + 1
with g : ℕ → ℕ
| 0     := 0
| (n+1) :=
  /- The following is a hint for the equation compiler.
     We will be able to delete it as soon as we have decision procedures for arithmetic -/
  have 2 + n * 2 < 1 + 2 * (n + 1), from
    begin
      rw [left_distrib], simp,
      well_founded_tactics.cancel_nat_add_lt,
      tactic.comp_val
    end,
  f n
