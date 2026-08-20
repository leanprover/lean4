module

structure S where
  decls : Array Nat

structure E where
  s : S

structure Inp (s : S) where
  x : Nat

def myF (s : S) (_ : Inp s) : E := ⟨s⟩

def composed (s : S) (a b : Nat) : E :=
  let res := myF s ⟨a⟩
  myF res.s ⟨b⟩

-- Sanity check: with the linter off (default), no warning is emitted.
#guard_msgs in
set_option warn.sorry false in
example (s : S) (a b idx : Nat) (h1 : idx < s.decls.size)
    (h2 : idx < (composed s a b).s.decls.size) :
    (composed s a b).s.decls[idx]'h2 = s.decls[idx]'h1 := by
  unfold composed
  sorry

set_option linter.tacticCheckInstances true

/--
@ +4:2...17
warning: produced tactic goal is not type-correct at `.implicit` transparency; consider using propositional rewriting or marking some of the following as `@[implicit_reducible]`:
  composed
  myF
Full error:
  Application type mismatch: The argument
    h2
  has type
    @LT.lt Nat instLTNat idx (composed s a b).s.decls.size
  but is expected to have type
    @LT.lt Nat instLTNat idx
      (have res := myF s { x := a };
            myF res.s { x := b }).s.decls.size
  in the application
    (have res := myF s { x := a };
          myF res.s { x := b }).s.decls[idx]

Note: This linter can be disabled with `set_option linter.tacticCheckInstances false`
-/
#guard_msgs (positions := true) in
example (s : S) (a b idx : Nat) (h1 : idx < s.decls.size)
    (h2 : idx < (composed s a b).s.decls.size) :
    (composed s a b).s.decls[idx]'h2 = s.decls[idx]'h1 := by
  unfold composed
  rfl

/--
@ +3:2...5
warning: initial tactic goal is not type-correct at `.implicit` transparency; consider rephrasing the goal or marking some of the following as `@[implicit_reducible]`:
  composed
  myF
Full error:
  Application type mismatch: The argument
    h1
  has type
    @LT.lt Nat instLTNat idx s.decls.size
  but is expected to have type
    @LT.lt Nat instLTNat idx (composed s a b).s.decls.size
  in the application
    (composed s a b).s.decls[idx]

Note: This linter can be disabled with `set_option linter.tacticCheckInstances false`
-/
#guard_msgs (positions := true) in
example (s : S) (a b idx : Nat) (h1 : idx < s.decls.size) :
    (composed s a b).s.decls[idx] = s.decls[idx] := by
  rfl

/-!
The goal below is type-correct at `.implicit` transparency (`natZero` is `@[implicit_reducible]`,
so `X natZero` and `X 0` are defeq there), but `simp`/`rw` unify instance-implicit arguments at
`.instances`, where they are not. The linter reports the stale instance argument that
`simp only [natZero_def]` left behind.
-/

class X (n : Nat)

@[implicit_reducible]
def natZero := 0

instance instXNatZero : X natZero where

theorem natZero_def : natZero = 0 := rfl

def g (n : Nat) [X n] : Nat := n + 1

theorem g_eq {n} [X n] : g n = n + 1 := by
  simp [g]

/--
@ +1:27...+2:31
error: unsolved goals
⊢ g 0 = 1
---
@ +2:2...31
warning: produced tactic goal contains an instance argument whose type does not match at `.instances` transparency; `simp` and `rw` unify instance-implicit arguments at that transparency, so lemmas mentioning this instance will fail to apply:
  The instance argument
    instXNatZero
  has type
    X natZero
  but is expected to have type
    X 0
  in the application
    @g 0 instXNatZero

Note: This linter can be disabled with `set_option linter.tacticCheckInstances false`
-/
#guard_msgs (positions := true) in
example : g natZero = 1 := by
  simp only [natZero_def, g_eq]

/-!
The mismatch has to survive down to `.instances` transparency: with an `@[instance_reducible]`
value the instance argument still matches there, so `g_eq` applies and the linter stays quiet.
-/

@[instance_reducible]
def natZeroI := 0

instance instXNatZeroI : X natZeroI where

theorem natZeroI_def : natZeroI = 0 := rfl

#guard_msgs in
example : g natZeroI = 1 := by
  simp only [natZeroI_def, g_eq]
