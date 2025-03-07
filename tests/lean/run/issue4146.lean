set_option linter.unusedVariables false

def bar (n : Nat) : Bool :=
  if h : n = 0 then
    true
  else
    match n with -- NB: the elaborator adds `h` as an discriminant
    | m+1 => bar m
termination_by n

-- set_option pp.match false
-- #print bar
-- #check bar.match_1
-- #print bar.induct

-- NB: The induction theorem used to ahve two `h` in scope, as its original type mentioning `x`,
-- and a refined `h` mentioning `m+1`.
-- At some point we had a HEq between them, but not any more, thanks to proof irrelevance
-- Since #7110, we drop the shadowed `h`.

/--
info: bar.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (m : Nat), ¬m + 1 = 0 → motive m → motive m.succ)
  (n : Nat) : motive n
-/
#guard_msgs in
#check bar.induct

def baz (n : Nat) (i : Fin (n+1)) : Bool :=
  if h : n = 0 then
    true
  else
    match n, i + 1 with
    | 1, _ => true
    | m+2, j => baz (m+1) ⟨j.1-1, by omega⟩
termination_by n

-- #print baz._unary

/--
info: baz.induct (motive : (n : Nat) → Fin (n + 1) → Prop) (case1 : ∀ (i : Fin (0 + 1)), motive 0 i)
  (case2 : ¬1 = 0 → ∀ (i : Fin (1 + 1)), motive 1 i)
  (case3 :
    ∀ (m : Nat), ¬m + 2 = 0 → ∀ (i : Fin (m.succ.succ + 1)), motive (m + 1) ⟨↑(i + 1) - 1, ⋯⟩ → motive m.succ.succ i)
  (n : Nat) (i : Fin (n + 1)) : motive n i
-/
#guard_msgs in
#check baz.induct
