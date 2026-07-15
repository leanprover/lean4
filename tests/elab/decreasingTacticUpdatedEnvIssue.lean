def g (x : Nat) (b : Bool) :=
  if b then
    x - 1
  else
    x + 1

theorem g_eq (x : Nat) (h : ¬ x = 0) : g x (x > 0) = x - 1 ∧ g x false = x + 1 := by
  have : x > 0 := by match x with
    | 0 => contradiction
    | x+1 => apply Nat.zero_lt_succ
  simp [g, this]

macro_rules
| `(tactic| decreasing_tactic) =>
 `(tactic|
   (simp [invImage, InvImage, Prod.lex, sizeOfWFRel, measure, Nat.lt_wfRel, WellFoundedRelation.rel, g_eq, *]
    apply Nat.pred_lt; assumption))

def f (x : Nat) : Nat :=
  if h : x = 0 then
    1
  else
    f (g x (x > 0)) + 2
termination_by x
