/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform

namespace Lean.Meta

/--
  Convert `ite` expressions in `e` to `dite`s.
  It is useful to make this conversion in the `WF` module because the condition is often used in
  termination proofs. -/
def iteToDIte (e : Expr) : MetaM Expr := do
  -- TODO: move this file to `Meta` if we decide to use it in other places.
  let post (e : Expr) : MetaM TransformStep := do
    if e.isAppOfArity ``ite 5 then
      let f    := e.getAppFn
      let args := e.getAppArgs
      let c    := args[1]!
      let h    ← mkFreshUserName `h
      let args := args.set! 3 (Lean.mkLambda h BinderInfo.default c args[3]!)
      let args := args.set! 4 (Lean.mkLambda h BinderInfo.default (mkNot c) args[4]!)
      return .done <| mkAppN (mkConst ``dite f.constLevels!) args
    else
      return .done e
  transform e (post := post)

end Lean.Meta
