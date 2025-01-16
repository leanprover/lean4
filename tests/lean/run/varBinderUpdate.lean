/-!
  # Changing variable binder annotations

  Tests the use of the `variable` command to update the binder annotations of existing variables. -/

/-! Test updating between default and implicit annotations. -/

namespace Ex1

variable {α : Type}
variable [Add α]
variable (α)
def f (a : α) := a + a
/--
info: f Nat 5 : Nat
-/
#guard_msgs in
#check f Nat 5
variable {α}
def g (b : α) := b
/--
info: g 5 : Nat
-/
#guard_msgs in
#check g 5
/--
info: Ex1.f (α : Type) [Add α] (a : α) : α
-/
#guard_msgs in
#check f
/--
info: Ex1.g {α : Type} (b : α) : α
-/
#guard_msgs in
#check g
end Ex1

namespace Ex2

variable {α β : Type}
variable (α)
def f (a : α) := a
def g (b : β) := b
/--
info: f Nat 5 : Nat
-/
#guard_msgs in
#check f Nat 5
/--
info: g 5 : Nat
-/
#guard_msgs in
#check g 5
/--
info: Ex2.f (α : Type) (a : α) : α
-/
#guard_msgs in
#check f
/--
info: Ex2.g {β : Type} (b : β) : β
-/
#guard_msgs in
#check g
/--
error: redundant binder annotation update
-/
#guard_msgs in
variable (α)
end Ex2

namespace Ex3

variable {α : Type}
variable (f : α → α)
variable (α)
def g (a : α) := f a
/--
info: Ex3.g (α : Type) (f : α → α) (a : α) : α
-/
#guard_msgs in
#check g
variable {f}
def h (a : α) := f a
/--
info: Ex3.h (α : Type) {f : α → α} (a : α) : α
-/
#guard_msgs in
#check h
end Ex3

namespace Ex4

variable {α β : Type}
variable (α γ)
def g (a : α) (b : β) (c : γ) := (a, b, c)
/--
info: g Nat Bool 10 "hello" true : Nat × String × Bool
-/
#guard_msgs in
#check g Nat Bool 10 "hello" true
end Ex4

/-! Test updating from and to instance-implicit. -/

namespace Ex5

variable [i : Add α]
variable (i)
def f (x y : α) := x + y
/--
info: Ex5.f.{u_1} {α : Type u_1} (i : Add α) (x y : α) : α
-/
#guard_msgs in
#check f
variable [i]
def g (x y : α) := x + y
/--
info: Ex5.g.{u_1} {α : Type u_1} [i : Add α] (x y : α) : α
-/
#guard_msgs in
#check g
end Ex5

/-! Test that variables with default values/tactics cannot be updated. -/

namespace Ex6

variable (a : Nat)
variable (h : a = a := rfl)
/--
error: cannot update binder annotation of variables with default values/tactics
-/
#guard_msgs in
variable {h}
end Ex6

/-! Test that variables that cannot be instance-implicit fail to be updated thereto. -/

namespace Ex7

variable (n : Nat)
/--
error: cannot update binder annotation of variable 'n' to instance-implicit:
invalid binder annotation, type is not a class instance
  Nat
use the command `set_option checkBinderAnnotations false` to disable the check
-/
#guard_msgs in
variable [n]
variable (x)
/--
error: cannot update binder annotation of variable 'x' to instance-implicit:
variable was originally declared without an explicit type
-/
#guard_msgs in
variable [x]
end Ex7

/-! Test updating to and from strict-implicit annotations. -/

namespace Ex8

variable {α : Type} (β : Type)
variable ⦃α⦄
def f (a : α) (_ : β) := a
/--
info: Ex8.f ⦃α : Type⦄ (β : Type) (a : α) : β → α
-/
#guard_msgs in
#check f
variable (α)
variable ⦃β⦄
def g (a : α) (b : β) := (a, b)
/--
info: Ex8.g (α : Type) ⦃β : Type⦄ (a : α) (b : β) : α × β
-/
#guard_msgs in
#check g
variable {β}
def h (b : β) := b
/--
info: Ex8.h {β : Type} (b : β) : β
-/
#guard_msgs in
#check h
variable {{β}}
/--
error: redundant binder annotation update
-/
#guard_msgs in
variable ⦃β⦄
end Ex8
