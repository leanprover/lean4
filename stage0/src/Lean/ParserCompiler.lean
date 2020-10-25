/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

/-!
Gadgets for compiling parser declarations into other programs, such as pretty printers.
-/

import Lean.Util.ReplaceExpr
import Lean.Meta.Basic
import Lean.Meta.WHNF
import Lean.ParserCompiler.Attribute
import Lean.Parser.Extension

namespace Lean
namespace ParserCompiler

structure Context (α : Type) :=
(varName : Name)
(runtimeAttr : KeyedDeclsAttribute α)
(combinatorAttr : CombinatorAttribute)
(interpretParserDescr : ParserDescr → AttrM α)

def Context.tyName {α} (ctx : Context α) : Name := ctx.runtimeAttr.defn.valueTypeName

-- replace all references of `Parser` with `tyName` as a first approximation
def preprocessParserBody {α} (ctx : Context α) (e : Expr) : Expr :=
e.replace fun e => if e.isConstOf `Lean.Parser.Parser then mkConst ctx.tyName else none

section
open Meta

-- translate an expression of type `Parser` into one of type `tyName`
partial def compileParserBody {α} (ctx : Context α) (e : Expr) (force : Bool := false) : MetaM Expr := do
let e ← whnfCore e
match e with
| e@(Expr.lam _ _ _ _)     => lambdaLetTelescope e fun xs b => compileParserBody ctx b >>= mkLambdaFVars xs
| e@(Expr.fvar _ _)        => pure e
| _ => do
  let fn := e.getAppFn
  let Expr.const c _ _ ← pure fn
    | throwError! "call of unknown parser at '{e}'"
  let args := e.getAppArgs
  -- call the translated `p` with (a prefix of) the arguments of `e`, recursing for arguments
  -- of type `ty` (i.e. formerly `Parser`)
  let mkCall (p : Name) := do
    let ty ← inferType (mkConst p)
    forallTelescope ty fun params _ =>
      params.foldlM₂ (fun p param arg => do
        let paramTy ← inferType param
        let resultTy ← forallTelescope paramTy fun _ b => pure b
        let arg ← if resultTy.isConstOf ctx.tyName then compileParserBody ctx arg else pure arg
        pure $ mkApp p arg)
        (mkConst p)
        e.getAppArgs
  let env ← getEnv
  match ctx.combinatorAttr.getDeclFor env c with
  | some p => mkCall p
  | none   =>
    let c' := c ++ ctx.varName
    let cinfo ← getConstInfo c
    let resultTy ← forallTelescope cinfo.type fun _ b => pure b
    if resultTy.isConstOf `Lean.Parser.TrailingParser || resultTy.isConstOf `Lean.Parser.Parser then do
      -- synthesize a new `[combinatorAttr c]`
      let some value ← pure cinfo.value?
        | throwError! "don't know how to generate {ctx.varName} for non-definition '{e}'"
      unless (env.getModuleIdxFor? c).isNone || force do
        throwError! "refusing to generate code for imported parser declaration '{c}'; use `@[runParserAttributeHooks]` on its definition instead."
      let value ← compileParserBody ctx $ preprocessParserBody ctx value
      let ty ← forallTelescope cinfo.type fun params _ =>
        params.foldrM (init := mkConst ctx.tyName) fun param ty => do
          let paramTy ← inferType param;
          let paramTy ← forallTelescope paramTy fun _ b => pure $
            if b.isConstOf `Lean.Parser.Parser then mkConst ctx.tyName
            else b
          pure $ mkForall `_ BinderInfo.default paramTy ty
      let decl := Declaration.defnDecl {
        name := c', lparams := [],
        type := ty, value := value, hints := ReducibilityHints.opaque, isUnsafe := false }
      let env ← getEnv
      let env ← match env.addAndCompile {} decl with
        | Except.ok    env => pure env
        | Except.error kex => do throwError (← liftIO $ (kex.toMessageData {}).toString)
      setEnv $ ctx.combinatorAttr.setDeclFor env c c'
      mkCall c'
    else
      -- if this is a generic function, e.g. `HasAndthen.andthen`, it's easier to just unfold it until we are
      -- back to parser combinators
      let some e' ← unfoldDefinition? e
        | throwError! "don't know how to generate {ctx.varName} for non-parser combinator '{e}'"
      compileParserBody ctx e'
end

open Core

/-- Compile the given declaration into a `[(builtin)runtimeAttr declName]` -/
def compileParser {α} (ctx : Context α) (declName : Name) (builtin : Bool) (force := false) : AttrM Unit := do
-- This will also tag the declaration as a `[combinatorParenthesizer declName]` in case the parser is used by other parsers.
-- Note that simply having `[(builtin)Parenthesizer]` imply `[combinatorParenthesizer]` is not ideal since builtin
-- attributes are active only in the next stage, while `[combinatorParenthesizer]` is active immediately (since we never
-- call them at compile time but only reference them).
let (Expr.const c' _ _) ← (compileParserBody ctx (mkConst declName) force).run'
  | unreachable!
-- We assume that for tagged parsers, the kind is equal to the declaration name. This is automatically true for parsers
-- using `parser!` or `syntax`.
let kind := declName
addAttribute c' (if builtin then ctx.runtimeAttr.defn.builtinName else ctx.runtimeAttr.defn.name) (mkNullNode #[mkIdent kind])
-- When called from `interpretParserDescr`, `declName` might not be a tagged parser, so ignore "not a valid syntax kind" failures
<|> pure ()

unsafe def interpretParser {α} (ctx : Context α) (constName : Name) (force := false) : AttrM α := do
let info ← getConstInfo constName
let env ← getEnv
if info.type.isConstOf `Lean.Parser.TrailingParser || info.type.isConstOf `Lean.Parser.Parser then
  match ctx.runtimeAttr.getValues env constName with
  | p::_ => pure p
  | _    =>
    compileParser ctx constName (builtin := false) force
    evalConst α (constName ++ ctx.varName)
else
  let d ← evalConst TrailingParserDescr constName
  ctx.interpretParserDescr d

unsafe def registerParserCompiler {α} (ctx : Context α) : IO Unit := do
Parser.registerParserAttributeHook {
  postAdd := fun catName declName builtin => do
    -- force compilation of parser even if imported, which can be the case with `[runBuiltinParserAttributeHooks]`
    if builtin then
      compileParser ctx declName builtin (force := true)
    else
      let p ← interpretParser ctx declName (force := true)
      -- Register `p` without exporting it to the .olean file. It will be re-interpreted and registered
      -- when the parser is imported.
      let env ← getEnv
      setEnv $ ctx.runtimeAttr.ext.modifyState env fun st => { st with table := st.table.insert declName p }
}

end ParserCompiler
end Lean
