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
warning: produced tactic goal is not type-correct at `.instances` transparency; consider using propositional rewriting or marking some of the following as `@[implicit_reducible]`:
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
warning: initial tactic goal is not type-correct at `.instances` transparency; consider rephrasing the goal or marking some of the following as `@[implicit_reducible]`:
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
