import Lean
open Lean Meta Elab Term

elab "#reduce'" t:term : command => Elab.Command.runTermElabM fun _ => do
  let e ← withSynthesize <| elabTerm t none
  let e ← Meta.reduce e
  withTransparency TransparencyMode.all do
    logInfo m!"{← inferType e}"

structure S where
  x : Nat

def S' := S
def S'.x (s : S') : Nat := S.x s

attribute [irreducible] S'

variable (s : S')
#reduce' s.x
