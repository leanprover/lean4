/-!
# Ensure that `rw ... at h` does not create unknown free variables (issue #2711)

## Context

`rw ... at h` elaborates its rules with postponed metavariables, which, prior to this test, were
synthesized after the bulk of the tactic has taken place by `Term.withSynthesize`. Specifically,
these mvars were synthesized after `replaceLocalDecl` has executed.

`replaceLocalDecl` needs to be sure it's not inserting the new, rewritten hypothesis before any
fvars which the type of that hypothesis now depends on. For example, if the type of `h` got
rewritten to `f i` where `i` was a local declaration occurring after `h`, `replaceLocalDecl` should
insert the rewritten `h` after `i`.

To ensure this, it traverses the type looking for fvars to find the latest-occurring one. However,
the pending mvars it might encounter in the type have not even been assigned yet, and so
`replaceLocalDecl` will not find any fvars when it traverses over them. `Term.withSynthesize` might
nevertheless assign these mvars to later-occurring fvars afterwards. As such, the type of the
rewritten hypothesis might become ill-formed at the place `replaceLocalDecl` inserts it once the
pending mvars are assigned, as it might now include unknown `FVarId`s (the `FVarId`s following the
insertion spot will have been changed by the insertion).

This test reflects the choice to synthesize the pending mvars before `replaceLocalDecl` is
executed, thus avoiding this issue.
-/

class Bar (α) where a : α

def f {α} [Bar α] (a : α) := a

def w (_ : α) : Prop := True

theorem foo {a : α} [Bar α] : w a = w (f a) := rfl

set_option pp.explicit true in
example : True := by
  have h : w 5 := trivial
  let inst : Bar Nat := ⟨0⟩
  rw [foo] at h
  -- Previous goal state:
  /-
  h✝ : @w Nat 5
  h : @w Nat (@f Nat _uniq.158 5)
  inst : Bar Nat := @Bar.mk Nat 0
  ⊢ True
  -/
