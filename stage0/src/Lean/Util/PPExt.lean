/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Environment
import Lean.MetavarContext
import Lean.Data.OpenDecl

namespace Lean

builtin_initialize
  registerOption `syntaxMaxDepth { defValue := (2 : Nat), group := "", descr := "maximum depth when displaying syntax objects in messages" };
  registerOption `pp.raw { defValue := false, group := "pp", descr := "(pretty printer) print raw expression/syntax tree" }

def getSyntaxMaxDepth (opts : Options) : Nat :=
  opts.getNat `syntaxMaxDepth 2

def getPPRaw (opts : Options) : Bool :=
  opts.getBool `pp.raw false

structure PPContext :=
  (env           : Environment)
  (mctx          : MetavarContext := {})
  (lctx          : LocalContext := {})
  (opts          : Options := {})
  (currNamespace : Name := Name.anonymous)
  (openDecls     : List OpenDecl := [])

structure PPFns :=
  (ppExpr : PPContext → Expr → IO Format)
  (ppTerm : PPContext → Syntax → IO Format)

instance : Inhabited PPFns := ⟨⟨arbitrary, arbitrary⟩⟩

builtin_initialize ppFnsRef : IO.Ref PPFns ←
  IO.mkRef {
    ppExpr := fun ctx e   => pure $ format (toString e),
    ppTerm := fun ctx stx => pure $ stx.formatStx (getSyntaxMaxDepth ctx.opts),
  }

builtin_initialize ppExt : EnvExtension PPFns ←
  registerEnvExtension $ ppFnsRef.get

def ppExpr (ctx : PPContext) (e : Expr) : IO Format :=
  let e := ctx.mctx.instantiateMVars e |>.1
  if getPPRaw ctx.opts then
    pure $ format (toString e)
  else
    (ppExt.getState ctx.env).ppExpr ctx e

def ppTerm (ctx : PPContext) (stx : Syntax) : IO Format :=
  if getPPRaw ctx.opts then
    pure $ stx.formatStx (getSyntaxMaxDepth ctx.opts)
  else
    (ppExt.getState ctx.env).ppTerm ctx stx

end Lean
