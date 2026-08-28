/-
Standalone reproducer for universe level matching bug in Sym.Pattern.match?.

When matching `Spec.get_StateT` pattern against `MonadStateOf.get`, the pattern
has universe levels `[_uvar.0, max _uvar.0 _uvar.1]` while the expression has
`[0, u_1]`. The match fails because `processLevel` has no case for
`.max u₁ u₂` vs `.param _` — it falls through to `| _, _ => return false`.

The fix should substitute already-assigned uvars before the fallthrough, or add
a case that handles `.max` vs non-`.max` by trying to assign the remaining uvars.
-/
module

import Lean
import Std

open Lean Meta Sym Std Do

/--
info: Expression: MonadStateOf.get
---
info: Expr fn levels: [0, u_1]
---
info: Match SUCCEEDED: 2 levels, 6 args
-/
#guard_msgs in
#eval show MetaM Unit from do
  -- 1. Build the pattern from the spec theorem, keyed on the program
  let info ← getConstInfo ``Spec.get_StateT
  let levelParams := info.levelParams
  let proof := mkConst ``Spec.get_StateT (levelParams.map mkLevelParam)
  let (pat, _) ← Sym.mkPatternFromExprWithKey proof levelParams fun type => do
    let_expr Triple _m _ps _inst _α prog _P _Q := type
      | throwError "not a Triple: {type}"
    return (prog, ())

  -- 2. Build target: @MonadStateOf.get (Nat × Nat) (StateT (Nat × Nat) m) inst
  let u1 := Level.param `u_1
  let mTy ← mkArrow (mkSort 1) (mkSort u1.succ)
  withLocalDeclD `m mTy fun m => do
  let instMonadTy ← mkAppM ``Monad #[m]
  withLocalDeclD `inst_Monad instMonadTy fun _instMonad => do
    let σ := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat)
    let stateT := mkApp2 (mkConst ``StateT [.zero, u1]) σ m
    let instMSO ← synthInstance (mkApp2 (mkConst ``MonadStateOf [.zero, u1]) σ stateT)
    let e := mkApp3 (mkConst ``MonadStateOf.get [.zero, u1]) σ stateT instMSO
    logInfo m!"Expression: {e}"
    logInfo m!"Expr fn levels: {e.getAppFn.constLevels!}"

    -- 3. Try pattern matching
    let result ← SymM.run (pat.match? e)
    match result with
    | some res =>
      logInfo m!"Match SUCCEEDED: {res.us.length} levels, {res.args.size} args"
    | none =>
      logInfo m!"Match FAILED — this is the bug"
      logInfo m!"  Pattern fn levels: {pat.pattern.getAppFn.constLevels!}"
      logInfo m!"  Expression fn levels: {e.getAppFn.constLevels!}"
