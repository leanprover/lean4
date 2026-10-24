module

namespace SMI

@[expose] public def m (n : Nat) : Nat := n + 2

@[simp] public theorem m_zero : m 0 = 2 := rfl
-- private, so only in the private olean level
@[simp] theorem m_one : m 1 = 3 := rfl

end SMI
