prelude

import Lean.Attributes
import Lean.Meta.Basic
import Lean.Meta.WHNF
import Lean.Util.Recognizers

namespace Lean.Meta

def validateRflAttr (_declName : Name) : AttrM Unit := do
  -- let { kind := .thm, constInfo, .. } ← getAsyncConstInfo declName |
  --   throwError "Could not find {declName}"
  -- let .thmInfo _info ← traceBlock "isRflTheorem theorem body" constInfo |
    -- throwError "{declName} is not a theorem"
  -- TODO: Do the actual check
  pure ()

builtin_initialize rflAttr : TagAttribute ←
  registerTagAttribute `rfl "mark theorem as a `rfl`-theorem, to be used by `dsimp`"
    (validate := validateRflAttr) (applicationTime := .afterTypeChecking)
    (asyncMode := .async)



private partial def isRflProofCore (type : Expr) (proof : Expr) : CoreM Bool := do
  match type with
  | .forallE _ _ type _ =>
    if let .lam _ _ proof _ := proof then
      isRflProofCore type proof
    else
      return false
  | _ =>
    if type.isAppOfArity ``Eq 3 then
      if proof.isAppOfArity ``Eq.refl 2 || proof.isAppOfArity ``rfl 2 then
        return true
      else if proof.isAppOfArity ``Eq.symm 4 then
        -- `Eq.symm` of rfl theorem is a rfl theorem
        isRflProofCore type proof.appArg! -- small hack: we don't need to set the exact type
      else if proof.getAppFn.isConst then
        -- The application of a `rfl` theorem is a `rfl` theorem
        -- A constant which is a `rfl` theorem is a `rfl` theorem
        return rflAttr.hasTag (← getEnv) proof.getAppFn.constName!
      else
        return false
    else
      return false
/--
For
-/
def inferRflAttr (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let isRfl ←
    /-
    This did not work, it failed to recognize some proofs that definitely are refl.
    Maybe due to different whnf settings?

    withTransparency .all do -- TODO: Is this the right choice?
      -- withOptions (smartUnfolding.set · false) do
        forallTelescopeReducing info.type fun _ type => do
          let some (_, lhs, rhs) := type.eq? | return false
          let r ← isDefEq lhs rhs
          trace[debug] "inferRflAttr {.ofConstName declName}: {r}{indentExpr type}"
          pure r
    -/
    if let some value := info.value? then
      isRflProofCore info.type value
    else
      pure false
  if isRfl then
    unless (← getEnv).asyncMayContain declName do
      throwError "inferRflAttr: declaration {.ofConstName declName} is not from the present async context {(← getEnv).asyncPrefix?}"
    modifyEnv fun env => rflAttr.ext.addEntry env declName
