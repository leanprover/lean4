module

set_option backward.isDefEq.respectTransparency.types true

/-!
After `unfold`, the goal may become not type-correct at `instances` transparency
because hypotheses still refer to the pre-unfolded definition. When `rw`/`simp`
fails in such a goal, the error message should include a note about the
type-correctness issue.
-/

structure S where
  decls : Array Nat

structure E where
  s : S

structure Inp (s : S) where
  x : Nat

class C (β : S → Type) (f : (s : S) → β s → E) where
  decl_eq : ∀ (s : S) (input : β s)
    (idx : Nat) (h1 : idx < s.decls.size) (h2 : idx < (f s input).s.decls.size),
    (f s input).s.decls[idx]'h2 = s.decls[idx]'h1

def myF (s : S) (_ : Inp s) : E := ⟨s⟩

set_option warn.sorry false in
instance : C Inp myF where
  decl_eq := by intros; sorry

def composed (s : S) (a b : Nat) : E :=
  let res := myF s ⟨a⟩
  myF res.s ⟨b⟩

section rw

-- Without `unfold`, the note should NOT fire (goal is type-correct at `instances`)
/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (myF ?s ?input).s.decls[?idx]
in the target expression
  (composed s a b).s.decls[idx] = s.decls[idx]

s : S
a b idx : Nat
h1 : idx < s.decls.size
h2 : idx < (composed s a b).s.decls.size
⊢ (composed s a b).s.decls[idx] = s.decls[idx]
-/
#guard_msgs in
example (s : S) (a b idx : Nat) (h1 : idx < s.decls.size)
    (h2 : idx < (composed s a b).s.decls.size) :
    (composed s a b).s.decls[idx]'h2 = s.decls[idx]'h1 := by
  rw [C.decl_eq (f := myF)]

-- With `unfold`, the note SHOULD fire (`h2`'s type no longer matches after unfolding)
/--
Note: The target expression is not type-correct under the `instances` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps.
-/
#guard_msgs (substring := true) in
example (s : S) (a b idx : Nat) (h1 : idx < s.decls.size)
    (h2 : idx < (composed s a b).s.decls.size) :
    (composed s a b).s.decls[idx]'h2 = s.decls[idx]'h1 := by
  unfold composed
  rw [C.decl_eq (f := myF)]

-- The defeq abuse may already be part of the initial goal.
/--
Note: The target expression is not type-correct under the `instances` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps.
-/
#guard_msgs (substring := true) in
example (s : S) (a b idx : Nat) (h1 : idx < s.decls.size) :
    (composed s a b).s.decls[idx] = s.decls[idx] := by
  rw [C.decl_eq (f := myF)]

end rw

section simp

-- Without `unfold`, the note should NOT fire
/--
error: `simp` made no progress
-/
#guard_msgs in
example (s : S) (a b idx : Nat) (h1 : idx < s.decls.size)
    (h2 : idx < (composed s a b).s.decls.size) :
    (composed s a b).s.decls[idx]'h2 = s.decls[idx]'h1 := by
  simp (config := { zeta := false })

-- With `unfold`, the note SHOULD fire
/--
error: `simp` made no progress

Note: The target expression is not type-correct under the `instances` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
-/
#guard_msgs in
example (s : S) (a b idx : Nat) (h1 : idx < s.decls.size)
    (h2 : idx < (composed s a b).s.decls.size) :
    (composed s a b).s.decls[idx]'h2 = s.decls[idx]'h1 := by
  unfold composed
  simp (config := { zeta := false })

end simp
