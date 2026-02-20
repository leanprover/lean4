import Lean

structure IW : Type 1 where
  I : Type


set_option Elab.async false

def aux (iw: IW) (e : Nat) (sm : List iw.I)
  : Nat :=
  e

-- set_option wf.preprocess false
-- set_option trace.Elab.definition.wf true
-- set_option pp.raw true
-- set_option trace.Debug.Meta.Tactic.simp true

mutual
def aval (iw: IW) (n : Nat) (e : Nat) : Nat :=
  match n with
  | 0 => e
  | n' + 1 =>
      let e1 :=
        let input_map : List iw.I := [] --lifting RB
        let new_e := aux iw e input_map -- removing args RB
        avalCore iw n' new_e -- inlining RB
      avalCore iw n' e
termination_by (n, 0)

-- Inlining RB
def avalCore (iw: IW) (n' : Nat) (e : Nat) : Nat :=
  aval iw n' e
termination_by (n', 1)

end

example :
  (have x : Nat := id 1
  have y : Nat := id x + 1
  (fun (x : Fin y) => x)) = (fun x => x) := by
  simp -zetaUnused -zetaDelta -zeta only [id]
  rfl
