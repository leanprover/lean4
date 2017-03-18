local infix * := _root_.mul

namespace Y
def mul : bool → bool := λ b, b

example (m n : ℕ) : true :=
begin
definev k : ℕ := m * n,
definev a : bool := mul tt,
trivial
end
end Y


meta def is_mul : expr → option (expr × expr)
| ```(%%a * %%b) := some (a, b)
| _              := none
