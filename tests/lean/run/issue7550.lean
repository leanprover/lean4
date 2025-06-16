namespace Bug

open Nat

theorem div_rec_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

protected noncomputable def divCore (x y : Nat) (fuel : Nat) (hfuel : x < fuel): Nat :=
  match fuel with
  | 0 => by contradiction
  | succ fuel =>
    if h : 0 < y ∧ y ≤ x then
      have this := div_rec_lemma h
      Bug.divCore (x - y) y fuel (Nat.lt_of_lt_of_le (div_rec_lemma h) (Nat.le_of_lt_succ hfuel)) + 1
    else
      0
termination_by structural fuel

-- /--
-- info: { funIndName := `Bug.divCore.induct,
--   levelMask := #[],
--   params := #[Lean.Meta.FunIndParamKind.target, Lean.Meta.FunIndParamKind.param, Lean.Meta.FunIndParamKind.target,
--               Lean.Meta.FunIndParamKind.target] }
-- -/
-- #guard_msgs in
-- run_meta
--   let some x ← Lean.Meta.getFunIndInfo? false ``Bug.divCore | return
--   Lean.logInfo m!"{repr x}"

/--
error: tactic 'fail' failed
case case1
x y fuel x✝ : Nat
hfuel✝ : x✝ < 0
⊢ Bug.divCore x✝ y 0 hfuel✝ = 42

case case2
x y fuel x✝ fuel✝ : Nat
hfuel✝ : x✝ < fuel✝.succ
h✝ : 0 < y ∧ y ≤ x✝
this✝ : x✝ - y < x✝
ih1✝ : Bug.divCore (x✝ - y) y fuel✝ ⋯ = 42
⊢ Bug.divCore x✝ y fuel✝.succ hfuel✝ = 42

case case3
x y fuel x✝ fuel✝ : Nat
hfuel✝ : x✝ < fuel✝.succ
h✝ : ¬(0 < y ∧ y ≤ x✝)
⊢ Bug.divCore x✝ y fuel✝.succ hfuel✝ = 42
-/
#guard_msgs(error) in
protected theorem divCore_eq_div : Bug.divCore x y fuel h = 42 := by
  fun_induction Bug.divCore
  fail

/--
error: tactic 'fail' failed
case case1
x y fuel x✝ : Nat
hfuel✝ : x✝ < 0
⊢ Bug.divCore x✝ y 0 hfuel✝ = 42

case case2
x y fuel x✝ fuel✝ : Nat
hfuel✝ : x✝ < fuel✝.succ
h✝ : 0 < y ∧ y ≤ x✝
this✝ : x✝ - y < x✝
ih1✝ : Bug.divCore (x✝ - y) y fuel✝ ⋯ = 42
⊢ Bug.divCore x✝ y fuel✝.succ hfuel✝ = 42

case case3
x y fuel x✝ fuel✝ : Nat
hfuel✝ : x✝ < fuel✝.succ
h✝ : ¬(0 < y ∧ y ≤ x✝)
⊢ Bug.divCore x✝ y fuel✝.succ hfuel✝ = 42
-/
#guard_msgs in
protected theorem divCore_eq_div' : Bug.divCore x y fuel h = 42 := by
  induction x, fuel, h using Bug.divCore.induct y
  fail

end Bug
