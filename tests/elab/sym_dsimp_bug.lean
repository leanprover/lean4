/-! # Regression test for `Sym.dsimp` binder handling

`dsimp` introduces telescope binders by re-instantiating each binder's type/value
against the free variables already introduced. A previous version created the local
declarations from the *raw* binder type/value, leaving loose bound variables that were
later misinterpreted when the declaration was zeta-expanded under a different binder
(here the `_unit` lambda), producing an ill-typed term the kernel rejected. -/

inductive Effects where
  | done_val : BitVec 64 → Effects
  | other : Effects
  | require_exec_access : (Unit → Effects) → Effects

def Effects.All (post : Effects → Prop) : Effects → Prop
  | .done_val v => post (.done_val v)
  | .other => False
  | .require_exec_access cont => (cont ()).All post

structure MyState where
  zf : Bool

register_sym_dsimp myVariant where
  pre := proj

set_option warn.sorry false

theorem test_error (x : BitVec 64) (post : Effects → Prop) :
    let v := x + 1
    let status := MyState.mk (v == 0)
    Effects.All post (Effects.require_exec_access (fun _unit => if status.zf then Effects.done_val v else Effects.other)) := by
  sym =>
  dsimp myVariant
  sorry
