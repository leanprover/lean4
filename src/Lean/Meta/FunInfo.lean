/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.InferType
import Init.Data.Range.Polymorphic.Iterators

public section

namespace Lean.Meta

private structure FunInfoEnvCacheKey where
  c : Name
  ls : List Level
  maxArgs? : Option Nat
deriving BEq, Hashable, TypeName

@[inline] private def checkFunInfoCache (fn : Expr) (maxArgs? : Option Nat) (k : MetaM FunInfo) : MetaM FunInfo := do
  let key ← mkInfoCacheKey fn maxArgs?
  match (← get).cache.funInfo.find? key with
  | some finfo => return finfo
  | none       => do
    let finfo ← match fn with
      | .const c ls =>
        -- If `fn` is only a single constant, we can share the result with any thread that can see `c`
        -- as well.
        if ls.any (·.hasMVar) then
          -- However, if any level mvars are present, other threads should not be able to encounter
          -- the same `fn` and sharing would just waste time.
          k
        else
          realizeValue c { c, ls, maxArgs? : FunInfoEnvCacheKey } k
      | _ => k
    modify fun s => { s with cache := { s.cache with funInfo := s.cache.funInfo.insert key finfo } }
    return finfo

@[inline] private def whenHasVar {α} (e : Expr) (deps : α) (k : α → α) : α :=
  if e.hasFVar then k deps else deps

private def collectDeps (fvars : Array Expr) (e : Expr) : Array Nat :=
  let rec visit (e : Expr) (deps : Array Nat) : Array Nat :=
    match e with
    | .app f a         => whenHasVar e deps (visit a ∘ visit f)
    | .forallE _ d b _ => whenHasVar e deps (visit b ∘ visit d)
    | .lam _ d b _     => whenHasVar e deps (visit b ∘ visit d)
    | .letE _ t v b _  => whenHasVar e deps (visit b ∘ visit v ∘ visit t)
    | .proj _ _ e      => visit e deps
    | .mdata _ e       => visit e deps
    | .fvar ..         =>
      match fvars.idxOf? e with
      | none   => deps
      | some i => if deps.contains i then deps else deps.push i
    | _ => deps
  let deps := visit e #[]
  deps.qsort (fun i j => i < j)

/-- Update `hasFwdDeps` fields using new `backDeps` -/
private def updateHasFwdDeps (pinfo : Array ParamInfo) (backDeps : Array Nat) : Array ParamInfo :=
  if backDeps.size == 0 then
    pinfo
  else
    -- update hasFwdDeps fields
    pinfo.mapIdx fun i info =>
      if info.hasFwdDeps then
        info
      else if backDeps.contains i then
        { info with hasFwdDeps := true }
      else
        info

private def getFunInfoAux (fn : Expr) (maxArgs? : Option Nat) : MetaM FunInfo :=
  checkFunInfoCache fn maxArgs? do
    let fnType ← inferType fn
    withAtLeastTransparency TransparencyMode.default do
      forallBoundedTelescope fnType maxArgs? fun fvars type => do
        let mut paramInfo := #[]
        let mut higherOrderOutParams : FVarIdSet := {}
        for h : i in *...fvars.size do
          let fvar := fvars[i]
          let decl ← getFVarLocalDecl fvar
          let backDeps := collectDeps fvars decl.type
          let dependsOnHigherOrderOutParam :=
            !higherOrderOutParams.isEmpty
            && Option.isSome (decl.type.find? fun e => e.isFVar && higherOrderOutParams.contains e.fvarId!)
          let className? ← isClass? decl.type
          /-
          **Note**: We use `isClass? decl.type` instead of relying solely on binder annotations
          (`[...]`) because users sometimes use implicit binders for class types when the instance
          is already available from context. For example:
          ```
          structure OrdSet (α : Type) [Hashable α] [BEq α] where ...
          def OrdSet.insert {_ : Hashable α} {_ : BEq α} (s : OrdSet α) (a : α) : OrdSet α := ...
          ```
          Here, `Hashable` and `BEq` are classes, but implicit binders are used because the
          instances come from `OrdSet`'s parameters.

          However, we also require the binder to be non-explicit because structures extending
          classes use explicit binders for their constructor parameters:
          ```
          structure MyGroupTopology (α : Type) extends MyTopology α, IsContinuousMul α
          -- Constructor type:
          -- MyGroupTopology.mk (toMyTopology : MyTopology α) (toIsContinuousMul : IsContinuousMul α) : ...
          ```
          These explicit parameters should not be treated as instances for automation purposes.

          -/
          let isInstance := className?.isSome && !decl.binderInfo.isExplicit
          paramInfo := updateHasFwdDeps paramInfo backDeps
          paramInfo := paramInfo.push {
            backDeps, dependsOnHigherOrderOutParam, isInstance
            binderInfo := decl.binderInfo
            isProp     := (← isProp decl.type)
            isDecInst  := (← forallTelescopeReducing decl.type fun _ type => return type.isAppOf ``Decidable)
          }
          if isInstance then
            /- Collect higher order output parameters of this class IF `isInstance` is `true` -/
            let some className := className? | unreachable!
            /- Collect higher order output parameters of this class IF `isInstance` is `true` -/
            if let some outParamPositions := getOutParamPositions? (← getEnv) className then
              unless outParamPositions.isEmpty do
                let args := decl.type.getAppArgs
                for h2 : i in *...args.size do
                  if outParamPositions.contains i then
                    let arg := args[i]
                    if let some idx := fvars.idxOf? arg then
                      if (← whnf (← inferType arg)).isForall then
                        paramInfo := paramInfo.modify idx fun info => { info with higherOrderOutParam := true }
                        higherOrderOutParams := higherOrderOutParams.insert arg.fvarId!
        let resultDeps := collectDeps fvars type
        paramInfo := updateHasFwdDeps paramInfo resultDeps
        return { resultDeps, paramInfo }

def getFunInfo (fn : Expr) (maxArgs? : Option Nat := none) : MetaM FunInfo :=
  getFunInfoAux fn maxArgs?

def getFunInfoNArgs (fn : Expr) (nargs : Nat) : MetaM FunInfo :=
  getFunInfoAux fn (some nargs)

def FunInfo.getArity (info : FunInfo) : Nat :=
  info.paramInfo.size

end Lean.Meta
