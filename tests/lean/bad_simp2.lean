import tactic
universe U >= 2
variable f (A : (Type 1)) : (Type 1)
axiom Ax1 (a : Type) : f a = a
rewrite_set S
add_rewrite Ax1 eq_id : S
theorem T1a (A : Type) : f A = A
:= by simp S

-- The following theorem should not be provable.
-- The axiom Ax1 is only for arguments convertible to Type (i.e., Type 0)
-- The argument A in the following theorem lives in (Type 1)
theorem T1b (A : (Type 1)) : f A = A
:= by simp S

variable g (A : Type → (Type 1)) : (Type 1)
axiom Ax2 (a : Type → Type) : g a = a Bool
add_rewrite Ax2 : S
theorem T2a (A : Type → Type) : g A = A Bool
:= by simp S
-- The following theorem should not be provable.
-- See T1b
theorem T2b (A : Type → (Type 1)) : g A = A Bool
:= by simp S


variable h (A : Type) (B : (Type 1)) : (Type 1)
axiom Ax3 (a : Type) : h a a = a
add_rewrite Ax3 : S
theorem T3a (A : Type) : h A A = A
:= by simp S

axiom Ax4 (a b : Type) : h a b = b
add_rewrite Ax4 : S
theorem T4a (A : Type) (B : Type) : h A B = B
:= by simp S
-- The following theorem should not be provable.
-- See T1b
theorem T4b (A : Type) (B : (Type 1)) : h A B = B
:= by simp S

variable h2 (A : Type) (B : (Type 1)) : Type
axiom Ax5 (a b : Type) : f a = a -> h2 a b = a
add_rewrite Ax5 : S
theorem T5a (A B : Type) : h2 A B = A
:= by simp S

-- The following theorem should not be provable.
-- See T1b
theorem T5b (A : Type) (B : (Type 1)) : h2 A B = A
:= by simp S

print environment 1