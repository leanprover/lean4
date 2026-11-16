import Lean

/-!
Tests the `linter.csimpNoncomputable` linter, which warns when a
`@[csimp]` theorem replaces a definition that is not `noncomputable`.
-/

def f (n : Nat) : Nat := n
def fImpl (n : Nat) : Nat := n
theorem f_eq : @f = @fImpl := rfl

/-! The linter is off by default. -/

#guard_msgs in
attribute [csimp] f_eq

def g (n : Nat) : Nat := n
def gImpl (n : Nat) : Nat := n

/--
warning: `g` is replaced by a `@[csimp]` theorem but is not marked `noncomputable`, so code compiled before this theorem may still use the slow definition.

Note: This linter can be disabled with `set_option linter.csimpNoncomputable false`
-/
#guard_msgs in
set_option linter.csimpNoncomputable true in
@[csimp] theorem g_eq : @g = @gImpl := rfl

/-!
The linter is part of the `linter.coreInternal` set. The test runner passes `-Dlinter.all=false`,
which disables set-based enabling, so we check the set membership directly.
-/

/-- info: #[`linter.coreInternal] -/
#guard_msgs in
open Lean in
#eval show CoreM _ from return (← Linter.getLinterOptions).getSet linter.csimpNoncomputable

set_option linter.csimpNoncomputable true

/-! The linter can be disabled locally. -/

def k (n : Nat) : Nat := n
def kImpl (n : Nat) : Nat := n

#guard_msgs in
set_option linter.csimpNoncomputable false in
@[csimp] theorem k_eq : @k = @kImpl := rfl

/-! `noncomputable` definitions are fine. -/

noncomputable def nc (n : Nat) : Nat := n
def ncImpl (n : Nat) : Nat := n

#guard_msgs in
@[csimp] theorem nc_eq : @nc = @ncImpl := rfl

/-!
`noncomputable section` only marks definitions that fail to compile as `noncomputable`, so it does
not help here.
-/

noncomputable section
def ncs (n : Nat) : Nat := n
end
def ncsImpl (n : Nat) : Nat := n

/--
warning: `ncs` is replaced by a `@[csimp]` theorem but is not marked `noncomputable`, so code compiled before this theorem may still use the slow definition.

Note: This linter can be disabled with `set_option linter.csimpNoncomputable false`
-/
#guard_msgs in
@[csimp] theorem ncs_eq : @ncs = @ncsImpl := rfl

/-! Universe-polymorphic replacement of an imported, computable definition. -/

def myId (a : α) : α := a

/--
warning: `id` is replaced by a `@[csimp]` theorem but is not marked `noncomputable`, so code compiled before this theorem may still use the slow definition.

Note: This linter can be disabled with `set_option linter.csimpNoncomputable false`
-/
#guard_msgs in
@[csimp] theorem id_eq_myId : @id = @myId := rfl

/-! Recursors and structure projections cannot be marked `noncomputable`, so they are exempt. -/

inductive MyNat where
  | zero
  | succ (n : MyNat)

#guard_msgs in
@[csimp] theorem myNat_rec_eq : @MyNat.rec = @MyNat.rec := rfl

structure Foo where
  x : Nat

#guard_msgs in
@[csimp] theorem foo_x_eq : @Foo.x = @Foo.x := rfl
