/-!
# Test for issue 9286
https://github.com/leanprover/lean4/issues/9286

Previously `simp` would create a type incorrect term.
The proximal issue was that the universe level metavariable in the type `a` was being
abstracted without abstracting `a` itself.
However, we should not be abstracting `a`; instead, simp arguments should be elaborated
with a new metacontext depth -- this is in part justified by the fact that elaboration
of simp arguments should not be assigning metavariables.
-/

inductive SomeThing.{u} : Prop where
  | mk (_ : PUnit.{u})

/-!
Previously `simp` would succeed and lead to a kernel typechecking error.
Now, `simp` correctly makes no progress.
-/
/-- error: `simp` made no progress -/
#guard_msgs in
set_option pp.universes true in
def testMe (a : PUnit) : PLift SomeThing := by
  constructor
  have := SomeThing.mk a
  simp only [SomeThing.mk a]
