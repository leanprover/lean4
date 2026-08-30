/-!
# `abstractMVars` should treat metavariables occuring in the local context as fixed

https://github.com/leanprover/lean4/issues/9286
-/

/-!
In this example, `simp` used to erroneously make progress.

If `a : PUnit.{?u.1}`, then `SomeThing.mk a : SomeThing.{?u.1}`.
The goal is `SomeThing.{?u.2}`.
The way `simp` handles supplied lemmas is that it applies `abstractMVars` after elaboration,
so that it can transport the lemma's metavariables to other local contexts.
It used to be that `abstractMVars` would result in `SomeThing.mk.{v} a` for a fresh level
parameter `v`, but this is not type correct. Furthermore, `simp` *thought* it could apply this
lemma since when it instantiated it with a fresh level metavariable its type unifies with `SomeThing.{?u.2}`.
Now `abstractMVars` treats metavariables that the fvar dependencies depend on as fixed,
so the lemma can no longer apply.
-/

inductive SomeThing.{u} : Prop where
  | mk (_ : PUnit.{u})

/-- error: `simp` made no progress -/
#guard_msgs in
set_option pp.universes true in
example : True := by
  have a : PUnit := PUnit.unit
  have : SomeThing := by
    /-
    a : PUnit.{?u.1}
    ⊢ SomeThing.{?u.2}
    -/
    simp only [SomeThing.mk a]
  trivial

/-!
In this case, `simp` succeeds since `SomeThing.mk PUnit.unit` has its own
universe level metavariables that are abstracted.
-/
/--
error: failed to infer universe levels in `have` declaration type
  SomeThing.{_}
-/
#guard_msgs in
set_option pp.mvars.anonymous false in
example : True := by
  have : SomeThing := by
    simp only [SomeThing.mk PUnit.unit]
  trivial
