import Lean

abbrev T.{u} : Unit := (fun (α : Sort u) => ()) PUnit.{u}

set_option pp.universes true

def unitUnique (x y : Unit) : x = y := by rfl

def testUnique.{u, v} : T.{u} = T.{v} := unitUnique _ _

def test.{u, v} : T.{u} = T.{v} := rfl

def test'.{u, v} : T.{u} = T.{v} := rfl (a := ())

theorem test''.{u, v} : T.{u} = T.{v} := by
  unfold T
  rfl

-- Use kernel defeq
def test'''.{u, v} : T.{u} = T.{v} :=  by
  run_tac do
    Lean.Elab.Tactic.closeMainGoalUsing `test''' fun t _ =>
      Lean.Meta.mkEqRefl t.eq?.get!.2.1

/--
info: def test'''.{u, v} : Eq.{1} T.{u} T.{v} :=
Eq.refl.{1} T.{u}
-/
#guard_msgs in
#print test'''
