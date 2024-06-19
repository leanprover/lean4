import Lean.Elab.Command

/--
error: application type mismatch
  ⟨Nat.lt_irrefl ↑(?m.58 n), Fin.is_lt (?m.58 n)⟩
argument
  Fin.is_lt (?m.58 n)
has type
  ↑(?m.58 n) < ?m.57 n : Prop
but is expected to have type
  ↑(?m.58 n) < ↑(?m.58 n) : Prop
-/
#guard_msgs in
def foo := fun n => (not_and_self_iff _).mp ⟨Nat.lt_irrefl _, Fin.is_lt _⟩

/--
error: type mismatch
  Fin.is_lt ?m.185
has type
  ↑?m.185 < ?m.184 : Prop
but is expected to have type
  ?a < ?a : Prop
---
error: unsolved goals
case a
⊢ Nat

this : ?a < ?a
⊢ True
-/
#guard_msgs in
def test : True := by
  have : ((?a : Nat) < ?a : Prop) := by
    refine Fin.is_lt ?_
    done
  done

open Lean Meta
/--
info: Defeq?: false
---
info: fun x_0 x_1 => x_1
-/
#guard_msgs in
run_meta do
  let mvarIdNat ← mkFreshExprMVar (.some (.const ``Nat []))
  let mvarIdFin ← mkFreshExprMVar (.some (.app (.const `Fin []) mvarIdNat))
  -- mvarIdNat.assign (.app (.const ``Fin.val []) mvaridFin))
  let b ← isDefEq mvarIdNat (mkApp2 (.const ``Fin.val []) mvarIdNat mvarIdFin)
  logInfo m!"Defeq?: {b}" -- prints true
  -- Now mvaridNat occurs in its own type
  -- This will stack overflow
  let r ← abstractMVars mvarIdFin (levels := false)
  logInfo m!"{r.expr}"
