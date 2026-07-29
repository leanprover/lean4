/-! # Section variable cache tests

`runTermElabM` caches the elaboration of section variables and reuses it for the commands of a
scope (see `Elab.cacheSectionVars` and `Lean.Elab.Command.SectionVarsCache`). These tests check
that the reuse is not observable, except for the documented resolution snapshot below.
-/

/-! A command can constrain the universe of a section variable without affecting the other
commands of the scope: the cache re-instantiates the level metavariables for each command. -/

section
variable {M : Type _}

theorem t1 (_h : M = Nat) : True := trivial
theorem t2 : M = M := rfl

/-- info: @t1 : ∀ {M : Type}, M = Nat → True -/
#guard_msgs in #check @t1

/-- info: @t2 : ∀ {M : Type u_1}, M = M -/
#guard_msgs in #check @t2
end

/-! A `_` placeholder in a binder type is solved per command; such blocks are not cached. -/

section
variable (n : _)

theorem t3 : n = (5 : Nat) → True := fun _ => trivial
theorem t4 : n = "s" → True := fun _ => trivial

/-- info: t3 : ∀ (n : Nat), n = 5 → True -/
#guard_msgs in #check @t3

/-- info: t4 : ∀ (n : String), n = "s" → True -/
#guard_msgs in #check @t4
end

/-! A new instance invalidates the cache: the instance-implicit arguments inside binder types
are re-synthesized after the instance table changes. -/

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

/-! The cache freezes how the identifiers in binder types resolve: a declaration made between
two commands of a scope does not change the meaning of the section variables of earlier
`variable` commands. Without the cache, `s2` would be about `Shadow.Nat`. -/

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

/-! The cache can be disabled. -/

section
set_option Elab.cacheSectionVars false

variable (m : Nat)

theorem t7 : m = m := rfl

/-- info: t7 : ∀ (m : Nat), m = m -/
#guard_msgs in #check @t7
end

/-! `include` and `omit` change the scope and so rebuild the cache. -/

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

/-! An auto-bound universe name in a binder type disables the cache for the block, so the
universe parameter names of the declarations do not change. -/

section
variable {γ : Sort u} (g : γ → γ)

theorem t11 : ∀ x : γ, g x = g x := fun _ => rfl
theorem t12 : ∀ x : γ, g x = g x := fun _ => rfl

/-- info: @t12 : ∀ {γ : Sort u_1} (g : γ → γ) (x : γ), g x = g x -/
#guard_msgs in #check @t12
end
