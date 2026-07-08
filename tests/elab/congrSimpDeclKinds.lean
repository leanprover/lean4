/-!
This test checks that `.congr_simp` theorems are generated for all manners of declarations,
not just definitions. This collaterally checks that all these things have `enableRealizationsFor` run for them.
-/

inductive Foo where | mk : Fin n → Foo

/--
info: theorem Foo.mk.congr_simp : ∀ {n : Nat} (a a_1 : Fin n), a = a_1 → Foo.mk a = Foo.mk a_1
-/
#guard_msgs in
#print sig Foo.mk.congr_simp
def Foo_mk := @Foo.mk

/-- info: Foo_mk.congr_simp {n : Nat} (a✝ a✝¹ : Fin n) : a✝ = a✝¹ → Foo_mk a✝ = Foo_mk a✝¹ -/
#guard_msgs in
#check Foo_mk.congr_simp

inductive Bar (n : Nat) : Fin n → Type

/-- info: theorem Bar.congr_simp : ∀ (n : Nat) (a a_1 : Fin n), a = a_1 → Bar n a = Bar n a_1 -/
#guard_msgs in #print sig Bar.congr_simp

opaque baz (n : Nat) : Fin n → Type

/-- info: theorem baz.congr_simp : ∀ (n : Nat) (a a_1 : Fin n), a = a_1 → baz n a = baz n a_1 -/
#guard_msgs in #print sig baz.congr_simp

axiom quux (n : Nat) : Fin n → Type

/-- info: theorem quux.congr_simp : ∀ (n : Nat) (a a_1 : Fin n), a = a_1 → quux n a = quux n a_1 -/
#guard_msgs in #print sig quux.congr_simp

unsafe def unsafe_f (n : Nat) (f : Fin n) : Nat := f

/--
info: unsafe def unsafe_f.congr_simp : ∀ (n : Nat) (f f_1 : Fin n), f = f_1 → unsafe_f n f = unsafe_f n f_1
-/
#guard_msgs in #print sig unsafe_f.congr_simp

unsafe axiom unsafe_ax (n : Nat) (f : Fin n) : Nat

/--
info: unsafe def unsafe_ax.congr_simp : ∀ (n : Nat) (f f_1 : Fin n), f = f_1 → unsafe_ax n f = unsafe_ax n f_1
-/
#guard_msgs in #print sig unsafe_ax.congr_simp

unsafe opaque unsafe_op (n : Nat) (f : Fin n) : Nat := f

/--
info: unsafe def unsafe_op.congr_simp : ∀ (n : Nat) (f f_1 : Fin n), f = f_1 → unsafe_op n f = unsafe_op n f_1
-/
#guard_msgs in #print sig unsafe_op.congr_simp
