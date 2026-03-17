import Lean

open Lean Meta

-- set_option trace.Meta.Closure true

/--
info: before: h.2
---
info: after: _proof_2 ?m.1 h
-/
#guard_msgs(pass trace, all) in
run_meta do
  have l := ← Lean.Meta.mkFreshExprMVar (mkConst ``True) (kind := .syntheticOpaque)
  let ty := mkAnd (mkConst ``True) (.letE `foo (mkConst ``True) l (mkConst ``True) false)
  withLocalDecl `h default ty fun x => do
    let e := mkProj ``And 1 x
    Lean.logInfo m!"before: {e}"
    -- works fine without this line
    let e ← Lean.Meta.mkAuxTheorem (mkConst ``True) e (zetaDelta := true) -- or false, not really relevant
    Lean.logInfo m!"after: {e}"
