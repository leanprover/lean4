/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Expr

namespace Lean.Compiler.LCNF

partial def mapFVarM [Monad m] (f : FVarId → m FVarId) (e : Expr) : m Expr := do
  match e with
  | .proj typ idx struct => return .proj typ idx (← mapFVarM f struct)
  | .app fn arg => return .app (← mapFVarM f fn) (← mapFVarM f arg)
  | .fvar fvarId => return .fvar (← f fvarId)
  | .lam arg ty body bi =>
    return .lam arg (← mapFVarM f ty) (← mapFVarM f body) bi
  | .forallE arg ty body bi =>
    return .forallE arg (←mapFVarM f ty) (← mapFVarM f body) bi
  | .letE var ty value body nonDep  =>
    return .letE var (← mapFVarM f ty) (← mapFVarM f value) (← mapFVarM f body) nonDep
  | .bvar .. | .sort .. => return e
  | .mdata .. | .const .. | .lit .. => return e
  | .mvar .. => unreachable!

partial def forFVarM [Monad m] (f : FVarId → m Unit) (e : Expr) : m Unit := do
  match e with
  | .proj _ _ struct => forFVarM f struct
  | .app fn arg =>
    forFVarM f fn
    forFVarM f arg
  | .fvar fvarId => f fvarId
  | .lam _ ty body .. =>
    forFVarM f ty
    forFVarM f body
  | .forallE _ ty body .. =>
    forFVarM f ty
    forFVarM f body
  | .letE _ ty value body ..  =>
    forFVarM f ty
    forFVarM f value
    forFVarM f body
  | .bvar .. | .sort .. => return
  | .mdata .. | .const .. | .lit .. => return
  | .mvar .. => unreachable!

end Lean.Compiler.LCNF
