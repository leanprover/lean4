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

-- NB: The induction theorem has both `h` in scope, as its original type mentioning `x`,
-- and a refined `h` mentioning `m+1`.
-- The former is redundant here, but will we always know that?
-- No HEq betwen the two `h`s due to proof irrelevance

/--
info: bar.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (x : Nat), ¬x = 0 → ∀ (m : Nat), ¬m + 1 = 0 → motive m → motive m.succ) (n : Nat) : motive n
-/
#guard_msgs in
#check bar.induct


-- NB: Here we get a (heterogenous!) equality relating
-- `i + 1  : Fin (n+1)` and `j : Fin (m + 2 + 1)`
--
-- There is also another `i_0 : Fin (m + 2 + 1)`
-- because the `match` syntax also adds `i` to the discriminants.
-- All a bit messy, hopefully cleaner induction principles can be
-- created in the future.

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
  (case2 : ∀ (n : Nat) (i : Fin (n + 1)), ¬n = 0 → ∀ (x i_1 : Fin (1 + 1)), HEq (i + 1) x → motive 1 i_1)
  (case3 :
    ∀ (n : Nat) (i : Fin (n + 1)),
      ¬n = 0 →
        ∀ (m : Nat) (j i_1 : Fin (m + 2 + 1)),
          ¬m + 2 = 0 → HEq (i + 1) j → motive (m + 1) ⟨↑j - 1, ⋯⟩ → motive m.succ.succ i_1)
  (n : Nat) (i : Fin (n + 1)) : motive n i
-/
#guard_msgs in
#check baz.induct
