/-! # Section variable cache tests

`runTermElabM` caches the elaboration of the section variables and reuses it for the commands of
a scope. See `Elab.cacheSectionVars` and `Lean.Elab.Command.SectionVarsCache`. These tests check
that the reuse makes no observable difference, except for the resolution of the identifiers.
-/

/-! A command constrains the universe of a section variable. The other commands of the scope keep
their own universes, because the cache makes fresh level metavariables for each command. -/

section
variable {M : Type _}

theorem t1 (_h : M = Nat) : True := trivial
theorem t2 : M = M := rfl

/-- info: @t1 : ∀ {M : Type}, M = Nat → True -/
#guard_msgs in #check @t1

/-- info: @t2 : ∀ {M : Type u_1}, M = M -/
#guard_msgs in #check @t2
end

/-! Each command solves a `_` placeholder in a binder type on its own. The cache does not take
such a block. -/

section
variable (n : _)

theorem t3 : n = (5 : Nat) → True := fun _ => trivial
theorem t4 : n = "s" → True := fun _ => trivial

/-- info: t3 : ∀ (n : Nat), n = 5 → True -/
#guard_msgs in #check @t3

/-- info: t4 : ∀ (n : String), n = "s" → True -/
#guard_msgs in #check @t4
end

/-! A new instance invalidates the cache. The elaboration synthesizes the arguments in the binder
types again. -/

class A (α : Type) where
class B (α : Type) [A α] where

instance a1 : A Nat := ⟨⟩

section
set_option linter.unusedSectionVars false

variable [inst : B Nat]
include inst

theorem t5 : True := trivial

instance (priority := high) a2 : A Nat := ⟨⟩

theorem t6 : True := trivial

/-- info: @t5 : ∀ [inst : @B Nat a1], True -/
#guard_msgs in
set_option pp.explicit true in #check @t5

/-- info: @t6 : ∀ [inst : @B Nat a2], True -/
#guard_msgs in
set_option pp.explicit true in #check @t6
end

/-! The cache keeps the resolution of the identifiers in the binder types. A declaration between
two commands of a scope does not change the section variables of an earlier `variable` command.
Without the cache, `s2` uses `Shadow.Nat`. -/

namespace Shadow
section
variable (x : Nat)

theorem s1 : x = x := rfl

def Nat := Unit

theorem s2 : x = x := rfl

/-- info: s1 : ∀ (x : _root_.Nat), x = x -/
#guard_msgs in #check @s1

/-- info: s2 : ∀ (x : _root_.Nat), x = x -/
#guard_msgs in #check @s2
end
end Shadow

/-! The option disables the cache. -/

section
set_option Elab.cacheSectionVars false

variable (m : Nat)

theorem t7 : m = m := rfl

/-- info: t7 : ∀ (m : Nat), m = m -/
#guard_msgs in #check @t7
end

/-! `include` and `omit` change the scope. The cache takes a new entry. -/

section
variable {p : Nat} (hp : p = 0)

include hp

theorem t8 : p = 0 := hp

theorem t9 : p + 0 = 0 := by rw [Nat.add_zero, hp]

omit hp in
theorem t10 : p = p := rfl

/-- info: @t8 : ∀ {p : Nat}, p = 0 → p = 0 -/
#guard_msgs in #check @t8

/-- info: @t10 : ∀ {p : Nat}, p = p -/
#guard_msgs in #check @t10
end

/-! An auto-bound universe name in a binder type stops the cache for the block. The universe
parameter names of the declarations stay the same. -/

section
variable {γ : Sort u} (g : γ → γ)

theorem t11 : ∀ x : γ, g x = g x := fun _ => rfl
theorem t12 : ∀ x : γ, g x = g x := fun _ => rfl

/-- info: @t12 : ∀ {γ : Sort u_1} (g : γ → γ) (x : γ), g x = g x -/
#guard_msgs in #check @t12
end

/-! Type-class synthesis finds a section-variable instance in the commands that reuse the cached
binders. -/

class Cls (α : Type) where
  val : α

def clsVal (α : Type) [Cls α] : α := Cls.val

section
variable [inst : Cls Nat]
include inst

theorem i1 : clsVal Nat = clsVal Nat := rfl
theorem i2 : clsVal Nat = clsVal Nat := rfl
-- `i3` is the first command of the scope that reuses the cached binders.
theorem i3 : clsVal Nat = clsVal Nat := rfl

/-- info: @i3 : ∀ [inst : Cls Nat], clsVal Nat = clsVal Nat -/
#guard_msgs in #check @i3
end

/-! The binder annotations of the section variables stay the same through the cached telescope. -/

section
variable {a : Nat} ⦃b : Nat⦄ (c : Nat)

theorem b1 : a + b + c = a + b + c := rfl
theorem b2 : a + b + c = a + b + c := rfl
theorem b3 : a + b + c = a + b + c := rfl

/-- info: @b3 : ∀ {a : Nat} ⦃b : Nat⦄ (c : Nat), a + b + c = a + b + c -/
#guard_msgs in #check @b3
end

/-! An erasure of an instance also invalidates the cache. -/

section
set_option linter.unusedSectionVars false

variable [inst : B Nat]
include inst

theorem e1 : True := trivial
theorem e2 : True := trivial
theorem e3 : True := trivial

attribute [-instance] a2

theorem e4 : True := trivial

/-- info: @e4 : ∀ [inst : @B Nat a1], True -/
#guard_msgs in
set_option pp.explicit true in #check @e4
end

/-! The cache does not take a block that auto-binds an implicit variable. Each command elaborates
the auto-bound binder again. -/

section
variable (g : γ → γ)

theorem ab1 : ∀ x, g x = g x := fun _ => rfl
theorem ab2 : ∀ x, g x = g x := fun _ => rfl
theorem ab3 : ∀ x, g x = g x := fun _ => rfl

/-- info: @ab3 : ∀ {γ : Sort u_1} (g : γ → γ) (x : γ), g x = g x -/
#guard_msgs in #check @ab3
end

/-! A new default instance invalidates the cache. Default instances take part in the elaboration
of the binder types. -/

structure Wrap where
  val : Nat

instance wrapOfNat (n : Nat) : OfNat Wrap n := ⟨⟨n⟩⟩

section
set_option linter.unusedSectionVars false

variable (h : 5 = 5)
include h

theorem di1 : True := trivial
theorem di2 : True := trivial

/-- info: di2 : (5 : Nat) = (5 : Nat) → True -/
#guard_msgs in
set_option pp.numericTypes true in #check @di2

attribute [default_instance 2000] wrapOfNat

theorem di3 : True := trivial

/-- info: di3 : (5 : Wrap) = (5 : Wrap) → True -/
#guard_msgs in
set_option pp.numericTypes true in #check @di3
end

/-! A `set_option ... in` prefix makes a temporary scope. The commands after the prefix reuse the
binders of the outer scope. -/

section
variable (y : Nat)

theorem p1 : y = y := rfl
theorem p2 : y = y := rfl

set_option maxHeartbeats 400000 in
theorem p3 : y = y := rfl

theorem p4 : y = y := rfl

/-- info: p4 : ∀ (y : Nat), y = y -/
#guard_msgs in #check @p4
end
