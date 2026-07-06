import Lean

/-!
# The `linter.checkDeclsAtImplicit` linter

`linter.checkDeclsAtImplicit` warns when a declaration's type is type-correct at `.default`
transparency but not at `.implicit` transparency, suggesting the semireducible definitions that
should be marked `@[implicit_reducible]`.

Because the check runs in `addDecl`, the warning fires for *every* declaration, including ones
synthesized by attributes such as `@[simps]` and `@[reassoc]` (here modeled with a hand-written
lemma whose type mentions a semireducible definition).
-/

structure Fn where
  toFun : Nat → Nat

/-- `MyFn` is semireducible, so it does not unfold at `.implicit` transparency. -/
def MyFn : Type := Fn

def idFn : MyFn := (⟨id⟩ : Fn)

/-! ## Disabled by default -/

#guard_msgs in
theorem idFn_toFun_off : (idFn : Fn).toFun = id := rfl

/-! ## Warn if linter is enabled -/

set_option linter.checkDeclsAtImplicit true in
/--
warning: declaration idFn_toFun is not type-correct at `.implicit` transparency; consider marking some of the following as `@[implicit_reducible]`:
  MyFn

Note: This linter can be disabled with `set_option linter.checkDeclsAtImplicit false`
-/
#guard_msgs in
theorem idFn_toFun : (idFn : Fn).toFun = id := rfl

/-! ## Don't warn when the type is well-typed at implicit transparency -/

set_option linter.checkDeclsAtImplicit true in
#guard_msgs in
theorem reflexive_eq : (1 : Nat) = 1 := rfl

/-!
## Warning disappears after marking `MyFn` as implicit-reducible

Note: Marking declarations as implicit-reducible will make the elaborator unfold them more often.
This comes at a performance cost. Users need to decide which declarations they actually want to make
more reducible. If unfolding is undesirable, the alternative is to avoid relying on complex
unfolding.
-/

attribute [implicit_reducible] MyFn

set_option linter.checkDeclsAtImplicit true in
#guard_msgs in
theorem idFn_toFun_fixed : (idFn : Fn).toFun = id := rfl
