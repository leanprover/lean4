import Lean

/-!
Tests that simp applies the equational lemmas in order. In particular,
a catch-all at the end is tried afte the others
-/

def foo : Bool → Nat → Nat
  | _, 0 => 0
  | .true, n+1 => foo .true n
  | _, n+1 => foo .false n
termination_by _ n => n

/-- info: foo.eq_1 (x✝ : Bool) : foo x✝ 0 = 0 -/
#guard_msgs in
#check foo.eq_1
/-- info: foo.eq_2 (n : Nat) : foo true n.succ = foo true n -/
#guard_msgs in
#check foo.eq_2
/-- info: foo.eq_3 (x✝ : Bool) (n : Nat) (x_3 : x✝ = true → False) : foo x✝ n.succ = foo false n -/
#guard_msgs in
#check foo.eq_3

-- In order to reliably check if simp is not attempting to rewrite with a certain lemma
-- we can look at te diagnostics. But simply dumping all diangostics is too noisy for a test,
-- so here we try to get our hands at the `Simp.Stats` and look there.
open Lean Meta Elab Tactic in
elab "simp_foo_with_check" : tactic =>
  withOptions (fun o => diagnostics.set o true) do withMainContext do
    let stx ← `(tactic|simp [foo])
    let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false)
    let stats ← dischargeWrapper.with fun discharge? => do
      simpLocation ctx simprocs discharge? (expandOptLocation stx.raw[5])
    unless stats.diag.triedThmCounter.toList.any (fun (o, _n) => o.key = ``foo.eq_2) do
        throwError "Simp did not try to use foo.eq_2, is this test still working?"
    for (origin, n) in stats.diag.triedThmCounter.toList do
      if origin.key = ``foo.eq_3 then
        throwError m!"Bad: Simp used foo.eq_3 {n} times"

example : foo true 1 = 0 := by
  simp_foo_with_check -- essentially simp [foo]
