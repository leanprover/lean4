import Lean.Elab.Command

set_option pp.mvars false

/--
error: application type mismatch
  ⟨Nat.lt_irrefl ↑(?_ n), Fin.is_lt (?_ n)⟩
argument
  Fin.is_lt (?_ n)
has type
  ↑(?_ n) < ?_ n : Prop
but is expected to have type
  ↑(?_ n) < ↑(?_ n) : Prop
-/
#guard_msgs in
def foo := fun n => (not_and_self_iff _).mp ⟨Nat.lt_irrefl _, Fin.is_lt _⟩

/--
error: type mismatch
  Fin.is_lt ?_
has type
  ↑?_ < ?_ : Prop
but is expected to have type
  ?_ < ?_ : Prop
---
error: unsolved goals
case a
⊢ Nat

this : ?_ < ?_
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
