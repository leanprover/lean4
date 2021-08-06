/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Util.ReplaceExpr
import Lean.Meta.Basic
import Lean.Meta.WHNF
import Lean.ParserCompiler.Attribute
import Lean.Parser.Extension

/-!
Gadgets for compiling parser declarations into other programs, such as pretty printers.
-/

namespace Lean
namespace ParserCompiler

structure Context (α : Type) where
  varName : Name
  categoryAttr : KeyedDeclsAttribute α
  combinatorAttr : CombinatorAttribute

def Context.tyName {α} (ctx : Context α) : Name := ctx.categoryAttr.defn.valueTypeName

-- replace all references of `Parser` with `tyName`
def replaceParserTy {α} (ctx : Context α) (e : Expr) : Expr :=
  e.replace fun e =>
    -- strip `optParam`
    let e := if e.isOptParam then e.appFn!.appArg! else e
    if e.isConstOf `Lean.Parser.Parser then mkConst ctx.tyName else none

section
open Meta

variable {α} (ctx : Context α) (force : Bool := false) in
/--
  Translate an expression of type `Parser` into one of type `tyName`, tagging intermediary constants with
  `ctx.combinatorAttr`. If `force` is `false`, refuse to do so for imported constants. -/
partial def compileParserExpr (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  match e with
  | e@(Expr.lam _ _ _ _)     => lambdaLetTelescope e fun xs b => compileParserExpr b >>= mkLambdaFVars xs
  | e@(Expr.fvar _ _)        => pure e
  | _ => do
    let fn := e.getAppFn
    let Expr.const c _ _ ← pure fn
      | throwError "call of unknown parser at '{e}'"
    let args := e.getAppArgs
    -- call the translated `p` with (a prefix of) the arguments of `e`, recursing for arguments
    -- of type `ty` (i.e. formerly `Parser`)
    let mkCall (p : Name) := do
      let ty ← inferType (mkConst p)
      forallTelescope ty fun params _ => do
        let mut p := mkConst p
        let args  := e.getAppArgs
        for i in [:Nat.min params.size args.size] do
          let param := params[i]
          let arg   := args[i]
          let paramTy ← inferType param
          let resultTy ← forallTelescope paramTy fun _ b => pure b
          let arg ← if resultTy.isConstOf ctx.tyName then compileParserExpr arg else pure arg
          p := mkApp p arg
        pure p
    let env ← getEnv
    match ctx.combinatorAttr.getDeclFor? env c with
    | some p => mkCall p
    | none   =>
      let c' := c ++ ctx.varName
      let cinfo ← getConstInfo c
      let resultTy ← forallTelescope cinfo.type fun _ b => pure b
      if resultTy.isConstOf `Lean.Parser.TrailingParser || resultTy.isConstOf `Lean.Parser.Parser then do
        -- synthesize a new `[combinatorAttr c]`
        let some value ← pure cinfo.value?
          | throwError "don't know how to generate {ctx.varName} for non-definition '{e}'"
        unless (env.getModuleIdxFor? c).isNone || force do
          throwError "refusing to generate code for imported parser declaration '{c}'; use `@[runParserAttributeHooks]` on its definition instead."
        let value ← compileParserExpr $ replaceParserTy ctx value
        let ty ← forallTelescope cinfo.type fun params _ =>
          params.foldrM (init := mkConst ctx.tyName) fun param ty => do
            let paramTy ← replaceParserTy ctx <$> inferType param
            pure $ mkForall `_ BinderInfo.default paramTy ty
        let decl := Declaration.defnDecl {
          name := c', levelParams := [],
          type := ty, value := value, hints := ReducibilityHints.opaque, safety := DefinitionSafety.safe }
        let env ← getEnv
        let env ← match env.addAndCompile {} decl with
          | Except.ok    env => pure env
          | Except.error kex => do throwError (← (kex.toMessageData {}).toString)
        setEnv $ ctx.combinatorAttr.setDeclFor env c c'
        mkCall c'
      else
        -- if this is a generic function, e.g. `AndThen.andthen`, it's easier to just unfold it until we are
        -- back to parser combinators
        let some e' ← unfoldDefinition? e
          | throwError "don't know how to generate {ctx.varName} for non-parser combinator '{e}'"
        compileParserExpr e'
end

open Core

/-- Compile the given declaration into a `[(builtin)categoryAttr declName]` -/
def compileCategoryParser {α} (ctx : Context α) (declName : Name) (builtin : Bool) : AttrM Unit := do
  -- This will also tag the declaration as a `[combinatorParenthesizer declName]` in case the parser is used by other parsers.
  -- Note that simply having `[(builtin)Parenthesizer]` imply `[combinatorParenthesizer]` is not ideal since builtin
  -- attributes are active only in the next stage, while `[combinatorParenthesizer]` is active immediately (since we never
  -- call them at compile time but only reference them).
  let (Expr.const c' _ _) ← (compileParserExpr ctx (mkConst declName) (force := false)).run'
    | unreachable!
  -- We assume that for tagged parsers, the kind is equal to the declaration name. This is automatically true for parsers
  -- using `leading_parser` or `syntax`.
  let kind := declName
  let attrName := if builtin then ctx.categoryAttr.defn.builtinName else ctx.categoryAttr.defn.name
  -- Create syntax node for a simple attribute of the form
  -- `def simple := leading_parser ident >> optional (ident <|> priorityParser)`
  let stx := Syntax.node `Lean.Parser.Attr.simple #[
    mkIdent attrName,
    mkNullNode #[mkIdent kind]
  ]
  Attribute.add c' attrName stx

variable {α} (ctx : Context α) in
def compileEmbeddedParsers : ParserDescr → MetaM Unit
  | ParserDescr.const _                => pure ()
  | ParserDescr.unary _ d              => compileEmbeddedParsers d
  | ParserDescr.binary _ d₁ d₂         => compileEmbeddedParsers d₁ *> compileEmbeddedParsers d₂
  | ParserDescr.parser constName       => discard $ compileParserExpr ctx (mkConst constName) (force := false)
  | ParserDescr.node _ _ d             => compileEmbeddedParsers d
  | ParserDescr.nodeWithAntiquot _ _ d => compileEmbeddedParsers d
  | ParserDescr.sepBy p _ psep _       => compileEmbeddedParsers p *> compileEmbeddedParsers psep
  | ParserDescr.sepBy1 p _ psep _      => compileEmbeddedParsers p *> compileEmbeddedParsers psep
  | ParserDescr.trailingNode _ _ _ d   => compileEmbeddedParsers d
  | ParserDescr.symbol _               => pure ()
  | ParserDescr.nonReservedSymbol _ _  => pure ()
  | ParserDescr.cat _ _                => pure ()

/-- Precondition: `α` must match `ctx.tyName`. -/
unsafe def registerParserCompiler {α} (ctx : Context α) : IO Unit := do
  Parser.registerParserAttributeHook {
    postAdd := fun catName constName builtin => do
      let info ← getConstInfo constName
      if info.type.isConstOf `Lean.ParserDescr || info.type.isConstOf `Lean.TrailingParserDescr then
        let d ← evalConstCheck ParserDescr `Lean.ParserDescr constName <|>
          evalConstCheck TrailingParserDescr `Lean.TrailingParserDescr constName
        compileEmbeddedParsers ctx d |>.run'
      else
        if catName.isAnonymous then
          -- `[runBuiltinParserAttributeHooks]` => force compilation even if imported, do not apply `ctx.categoryAttr`.
          discard (compileParserExpr ctx (mkConst constName) (force := true)).run'
        else
          compileCategoryParser ctx constName builtin
  }

end ParserCompiler
end Lean
