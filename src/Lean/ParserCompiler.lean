/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Lean.Meta.ReduceEval
import Lean.Meta.WHNF
import Lean.KeyedDeclsAttribute
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

/-- Replace all references of `Parser` with `tyName` -/
def replaceParserTy {α} (ctx : Context α) (e : Expr) : Expr :=
  e.replace fun e =>
    -- strip `optParam`
    let e := if e.isOptParam then e.appFn!.appArg! else e
    if e.isConstOf `Lean.Parser.Parser then mkConst ctx.tyName else none

open Meta Parser in
/-- Takes an expression of type `Parser`, and determines the syntax kind of the root node it produces. -/
partial def parserNodeKind? (e : Expr) : MetaM (Option Name) := do
  let reduceEval? e : MetaM (Option Name) := do
    try pure <| some (← reduceEval e) catch _ => pure none
  let e ← whnfCore e
  if e matches Expr.lam .. then
    lambdaLetTelescope e fun _ e => parserNodeKind? e
  else if e.isAppOfArity ``leadingNode 3 || e.isAppOfArity ``trailingNode 4 || e.isAppOfArity ``node 2 then
    reduceEval? (e.getArg! 0)
  else if e.isAppOfArity ``withAntiquot 2 then
    parserNodeKind? (e.getArg! 1)
  else forallTelescope (← inferType e.getAppFn) fun params _ => do
    let lctx ← getLCtx
    -- if there is exactly one parameter of type `Parser`, search there
    if let [(i, _)] := params.toList.enum.filter (lctx.getFVar! ·.2 |>.type.isConstOf ``Parser) then
      parserNodeKind? (e.getArg! i)
    else
      return none

section
open Meta

variable {α} (ctx : Context α) (builtin : Bool) (force : Bool) in
/--
  Translate an expression of type `Parser` into one of type `tyName`, tagging intermediary constants with
  `ctx.combinatorAttr`. If `force` is `false`, refuse to do so for imported constants. -/
partial def compileParserExpr (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  match e with
  | .lam ..  => lambdaLetTelescope e fun xs b => compileParserExpr b >>= mkLambdaFVars xs
  | .fvar .. => return e
  | _ => do
    let fn := e.getAppFn
    let .const c .. := fn | throwError "call of unknown parser at '{e}'"
    -- call the translated `p` with (a prefix of) the arguments of `e`, recursing for arguments
    -- of type `ty` (i.e. formerly `Parser`)
    let mkCall (p : Name) := do
      let ty ← inferType (mkConst p)
      forallTelescope ty fun params _ => do
        let mut p := mkConst p
        let args  := e.getAppArgs
        for i in [:Nat.min params.size args.size] do
          let param := params[i]!
          let arg   := args[i]!
          let paramTy ← inferType param
          let resultTy ← forallTelescope paramTy fun _ b => pure b
          let arg ← if resultTy.isConstOf ctx.tyName then compileParserExpr arg else pure arg
          p := mkApp p arg
        return p
    let env ← getEnv
    match ctx.combinatorAttr.getDeclFor? env c with
    | some p => mkCall p
    | none   =>
      let c' := c ++ ctx.varName
      let cinfo ← getConstInfo c
      let resultTy ← forallTelescope cinfo.type fun _ b => pure b
      if resultTy.isConstOf ``Lean.Parser.TrailingParser || resultTy.isConstOf ``Lean.Parser.Parser then do
        -- synthesize a new `[combinatorAttr c]`
        let some value ← pure cinfo.value?
          | throwError "don't know how to generate {ctx.varName} for non-definition '{e}'"
        unless (env.getModuleIdxFor? c).isNone || force do
          throwError "refusing to generate code for imported parser declaration '{c}'; use `@[run_parser_attribute_hooks]` on its definition instead."
        let value ← compileParserExpr <| replaceParserTy ctx value
        let ty ← forallTelescope cinfo.type fun params _ =>
          params.foldrM (init := mkConst ctx.tyName) fun param ty => do
            let paramTy ← replaceParserTy ctx <$> inferType param
            return mkForall `_ BinderInfo.default paramTy ty
        let decl := Declaration.defnDecl {
          name := c', levelParams := []
          type := ty, value := value, hints := ReducibilityHints.opaque, safety := DefinitionSafety.safe
        }
        addAndCompile decl
        modifyEnv (ctx.combinatorAttr.setDeclFor · c c')
        if cinfo.type.isConst then
          if let some kind ← parserNodeKind? cinfo.value! then
            -- If the parser is parameter-less and produces a node of kind `kind`,
            -- then tag the compiled definition as `[(builtin)Parenthesizer kind]`
            -- (or `[(builtin)Formatter kind]`, resp.)
            let attrName := if builtin then ctx.categoryAttr.defn.builtinName else ctx.categoryAttr.defn.name
            -- Create syntax node for a simple attribute of the form
            -- `def simple := leading_parser ident >> optional (ident <|> priorityParser)`
            let stx := mkNode `Lean.Parser.Attr.simple #[mkIdent attrName, mkNullNode #[mkIdent kind]]
            Attribute.add c' attrName stx
        mkCall c'
      else
        -- if this is a generic function, e.g. `AndThen.andthen`, it's easier to just unfold it until we are
        -- back to parser combinators
        let some e' ← unfoldDefinition? e
          | throwError "don't know how to generate {ctx.varName} for non-parser combinator '{e}'"
        compileParserExpr e'
end

variable {α} (ctx : Context α) (builtin : Bool) in
def compileEmbeddedParsers : ParserDescr → MetaM Unit
  | ParserDescr.const _                => pure ()
  | ParserDescr.unary _ d              => compileEmbeddedParsers d
  | ParserDescr.binary _ d₁ d₂         => compileEmbeddedParsers d₁ *> compileEmbeddedParsers d₂
  | ParserDescr.parser constName       => discard <| compileParserExpr ctx (mkConst constName) (builtin := builtin) (force := false)
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
      if info.type.isConstOf ``Lean.ParserDescr || info.type.isConstOf ``Lean.TrailingParserDescr then
        let d ← evalConstCheck ParserDescr `Lean.ParserDescr constName <|>
          evalConstCheck TrailingParserDescr `Lean.TrailingParserDescr constName
        compileEmbeddedParsers ctx d (builtin := builtin) |>.run'
      else
        -- `[run_builtin_parser_attribute_hooks]` => force compilation even if imported, do not apply `ctx.categoryAttr`.
        let force := catName.isAnonymous
        discard (compileParserExpr ctx (mkConst constName) (builtin := builtin) (force := force)).run'
  }

end ParserCompiler
end Lean
