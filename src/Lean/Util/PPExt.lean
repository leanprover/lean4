/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Environment
import Lean.MetavarContext
import Lean.Data.OpenDecl

namespace Lean

structure PPContext :=
(env           : Environment)
(mctx          : MetavarContext := {})
(lctx          : LocalContext := {})
(opts          : Options := {})
(currNamespace : Name := Name.anonymous)
(openDecls     : List OpenDecl := [])

abbrev PPExprFn := PPContext → Expr → IO Format

/- TODO: delete after we implement the new pretty printer in Lean -/
@[extern "lean_pp_expr"]
constant ppOld : Environment → MetavarContext → LocalContext → Options → Expr → Format := arbitrary _

def mkPPExprFnRef : IO (IO.Ref PPExprFn) := IO.mkRef (fun ctx e => pure $ ppOld ctx.env ctx.mctx ctx.lctx ctx.opts e)
@[init mkPPExprFnRef] def ppExprFnRef : IO.Ref PPExprFn := arbitrary _

def mkPPExprFnExtension : IO (EnvExtension PPExprFn) :=
registerEnvExtension $ ppExprFnRef.get

@[init mkPPExprFnExtension]
constant ppExprExt : EnvExtension PPExprFn := arbitrary _

def ppExpr (ctx : PPContext) (e : Expr) : IO Format :=
let e := (ctx.mctx.instantiateMVars e).1;
if ctx.opts.getBool `ppOld true then
  (ppExprExt.getState ctx.env) ctx e
else
  pure $ format (toString e)

-- TODO: remove after we remove ppOld
@[init] def ppOldOption : IO Unit :=
registerOption `ppOld { defValue := true, group := "", descr := "disable/enable old pretty printer" }

end Lean
