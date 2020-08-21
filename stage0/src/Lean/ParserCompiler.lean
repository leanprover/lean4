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

open Meta

structure Context (α : Type) :=
(varName : Name)
(runtimeAttr : KeyedDeclsAttribute α)
(combinatorAttr : CombinatorAttribute)
(interpretParserDescr : ParserDescr → StateT Environment IO α)

def Context.tyName {α} (ctx : Context α) : Name := ctx.runtimeAttr.defn.valueTypeName

-- replace all references of `Parser` with `tyName` as a first approximation
def preprocessParserBody {α} (ctx : Context α) (e : Expr) : Expr :=
e.replace fun e => if e.isConstOf `Lean.Parser.Parser then mkConst ctx.tyName else none

-- translate an expression of type `Parser` into one of type `tyName`
partial def compileParserBody {α} (ctx : Context α) : Expr → MetaM Expr | e => do
e ← whnfCore e;
match e with
| e@(Expr.lam _ _ _ _)     => Meta.lambdaTelescope e fun xs b => compileParserBody b >>= Meta.mkLambda xs
| e@(Expr.fvar _ _)        => pure e
| _ => do
  let fn := e.getAppFn;
  Expr.const c _ _ ← pure fn
    | throwError $ "call of unknown parser at '" ++ toString e ++ "'";
  let args := e.getAppArgs;
  -- call the translated `p` with (a prefix of) the arguments of `e`, recursing for arguments
  -- of type `ty` (i.e. formerly `Parser`)
  let mkCall (p : Name) := do {
    ty ← inferType (mkConst p);
    Meta.forallTelescope ty fun params _ =>
      params.foldlM₂ (fun p param arg => do
        paramTy ← inferType param;
        resultTy ← Meta.forallTelescope paramTy fun _ b => pure b;
        arg ← if resultTy.isConstOf ctx.tyName then compileParserBody arg
          else pure arg;
        pure $ mkApp p arg)
        (mkConst p)
        e.getAppArgs
  };
  env ← getEnv;
  match ctx.combinatorAttr.getDeclFor env c with
  | some p => mkCall p
  | none   => do
    let c' := c ++ ctx.varName;
    cinfo ← getConstInfo c;
    resultTy ← Meta.forallTelescope cinfo.type fun _ b => pure b;
    if resultTy.isConstOf `Lean.Parser.TrailingParser || resultTy.isConstOf `Lean.Parser.Parser then do
      -- synthesize a new `[combinatorAttr c]`
      some value ← pure cinfo.value?
        | throwError $ "don't know how to generate " ++ ctx.varName ++ " for non-definition '" ++ toString e ++ "'";
      value ← compileParserBody $ preprocessParserBody ctx value;
      ty ← Meta.forallTelescope cinfo.type fun params _ =>
        params.foldrM (fun param ty => do
          paramTy ← inferType param;
          paramTy ← Meta.forallTelescope paramTy fun _ b => pure $
            if b.isConstOf `Lean.Parser.Parser then mkConst ctx.tyName
            else b;
          pure $ mkForall `_ BinderInfo.default paramTy ty)
          (mkConst ctx.tyName);
      let decl := Declaration.defnDecl { name := c', lparams := [],
        type := ty, value := value, hints := ReducibilityHints.opaque, isUnsafe := false };
      env ← getEnv;
      env ← match env.addAndCompile {} decl with
      | Except.ok    env => pure env
      | Except.error kex => throwError $ toString $ fmt $ kex.toMessageData {};
      setEnv $ ctx.combinatorAttr.setDeclFor env c c';
      mkCall c'
    else do
      -- if this is a generic function, e.g. `HasAndthen.andthen`, it's easier to just unfold it until we are
      -- back to parser combinators
      some e' ← liftM $ unfoldDefinition? e
        | throwError $ "don't know how to generate " ++ ctx.varName ++ " for non-parser combinator '" ++ toString e ++ "'";
      compileParserBody e'

/-- Compile the given declaration into a `[(builtin)runtimeAttr declName]` -/
def compileParser {α} (ctx : Context α) (env : Environment) (declName : Name) (builtin : Bool) : IO Environment := do
-- This will also tag the declaration as a `[combinatorParenthesizer declName]` in case the parser is used by other parsers.
-- Note that simply having `[(builtin)Parenthesizer]` imply `[combinatorParenthesizer]` is not ideal since builtin
-- attributes are active only in the next stage, while `[combinatorParenthesizer]` is active immediately (since we never
-- call them at compile time but only reference them).
(Expr.const c' _ _, env) ← (do a ← compileParserBody ctx (mkConst declName); env ← getEnv; pure (a, env)).toIO env
  | unreachable!;
-- We assume that for tagged parsers, the kind is equal to the declaration name. This is automatically true for parsers
-- using `parser!` or `syntax`.
let kind := declName;
env.addAttribute c' (if builtin then ctx.runtimeAttr.defn.builtinName else ctx.runtimeAttr.defn.name) (mkNullNode #[mkIdent kind])
  -- When called from `interpretParserDescr`, `declName` might not be a tagged parser, so ignore "not a valid syntax kind" failures
  <|> pure env

unsafe def interpretParser {α} (ctx : Context α) (constName : Name)
    : StateT Environment IO α :=
fun env => match env.find? constName with
| none      => throw $ IO.userError ("unknow constant '" ++ toString constName ++ "'")
| some info =>
  if info.type.isConstOf `Lean.Parser.TrailingParser || info.type.isConstOf `Lean.Parser.Parser then
    match ctx.runtimeAttr.getValues env constName with
    | p::_ => pure (p, env)
    | _    => do
      env ← compileParser ctx env constName /- builtin -/ false;
      p ← IO.ofExcept $ env.evalConst α (constName ++ ctx.varName);
      pure (p, env)
  else do
    d ← IO.ofExcept $ env.evalConst TrailingParserDescr constName;
    ctx.interpretParserDescr d env

unsafe def registerParserCompiler {α} (ctx : Context α) : IO Unit := do
Parser.registerParserAttributeHook {
  postAdd := fun catName env declName builtin =>
    if builtin then
      compileParser ctx env declName builtin
    else do
      (p, env) ← interpretParser ctx declName env;
      -- Register `p` without exporting it to the .olean file. It will be re-interpreted and registered
      -- when the parser is imported.
      pure $ ctx.runtimeAttr.ext.modifyState env fun st => { st with table := st.table.insert declName p }
}

end ParserCompiler
end Lean
