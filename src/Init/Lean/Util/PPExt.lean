/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Lean.Environment
import Init.Lean.MetavarContext

namespace Lean

abbrev PPExprFn := Environment → MetavarContext → LocalContext → Options → Expr → Format

/- TODO: delete after we implement the new pretty printer in Lean -/
@[extern "lean_pp_expr"]
constant ppOld : Environment → MetavarContext → LocalContext → Options → Expr → Format := arbitrary _

def mkPPExprFnRef : IO (IO.Ref PPExprFn) := IO.mkRef ppOld
@[init mkPPExprFnRef] def PPExprFnRef : IO.Ref PPExprFn := arbitrary _

def mkPPExprFnExtension : IO (EnvExtension PPExprFn) :=
registerEnvExtension $ PPExprFnRef.get

@[init mkPPExprFnExtension]
constant ppExprExt : EnvExtension PPExprFn := arbitrary _

def ppExpr (env : Environment) (mctx : MetavarContext) (lctx : LocalContext) (opts : Options) (e : Expr) : Format :=
let e := (mctx.instantiateMVars e).1;
if opts.getBool `ppOld true then
  (ppExprExt.getState env) env mctx lctx opts e
else
  format (toString e)

-- TODO: remove after we remove ppOld
@[init] def ppOldOption : IO Unit :=
registerOption `ppOld { defValue := true, group := "", descr := "disable/enable old pretty printer" }

end Lean
