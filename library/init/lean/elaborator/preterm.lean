/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.lean.elaborator.basic

namespace Lean

abbrev PreTerm := Expr

abbrev PreTermElab := SyntaxNode → Elab PreTerm

abbrev PreTermElabTable : Type := HashMap SyntaxNodeKind PreTermElab

def mkBuiltinPreTermElabTable : IO (IO.Ref PreTermElabTable) :=  IO.mkRef {}

@[init mkBuiltinPreTermElabTable]
constant builtinPreTermElabTable : IO.Ref PreTermElabTable := default _

def addBuiltinPreTermElab (k : SyntaxNodeKind) (declName : Name) (elab : PreTermElab) : IO Unit :=
do m ← builtinPreTermElabTable.get;
   when (m.contains k) $
     throw (IO.userError ("invalid builtin term elaborator, elaborator for '" ++ toString k ++ "' has already been defined"));
   builtinPreTermElabTable.modify $ fun m => m.insert k elab

def declareBuiltinPreTermElab (env : Environment) (kind : SyntaxNodeKind) (declName : Name) : IO Environment :=
declareBuiltinElab env `Lean.addBuiltinPreTermElab kind declName

@[init] def registerBuiltinPreTermElabAttr : IO Unit :=
registerAttribute {
 name  := `builtinPreTermElab,
 descr := "Builtin preterm conversion elaborator, we use it to interface with the Lean3 elaborator",
 add   := fun env declName arg persistent => do {
   unless persistent $ throw (IO.userError ("invalid attribute 'builtinPreTermElab', must be persistent"));
   kind ← syntaxNodeKindOfAttrParam env `Lean.Parser.Term arg;
   match env.find declName with
   | none  => throw "unknown declaration"
   | some decl =>
     match decl.type with
     | Expr.const `Lean.PreTermElab _ => declareBuiltinPreTermElab env kind declName
     | _ => throw (IO.userError ("unexpected preterm elaborator type at '" ++ toString declName ++ "' `PreTermElab` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
}

def Expr.mkAnnotation (ann : Name) (e : Expr) :=
Expr.mdata (MData.empty.setName `annotation ann) e

private def dummy : Expr := Expr.const `Prop []

namespace Elab

partial def toLevel : Syntax → Elab Level
| stx => do
  match stx.getKind with
  | `Lean.Parser.Level.paren  => toLevel $ stx.getArg 1
  | `Lean.Parser.Level.max    => do
     let args := (stx.getArg 1).getArgs;
     first ← toLevel (args.get 0);
     args.mfoldlFrom (fun r arg => Level.max r <$> toLevel arg) first 1
  | `Lean.Parser.Level.imax   => do
     let args := (stx.getArg 1).getArgs;
     first ← toLevel (args.get 0);
     args.mfoldlFrom (fun r arg => Level.imax r <$> toLevel arg) first 1
  | `Lean.Parser.Level.hole   => pure $ Level.mvar Name.anonymous
  | `Lean.Parser.Level.num    => pure $ Level.ofNat $ (stx.getArg 0).toNat
  | `Lean.Parser.Level.ident  => do
     let id := stx.getIdAt 0;
     univs ← getUniverses;
     if univs.elem id then pure $ Level.param id
     else do
       logError stx ("unknown universe variable '" ++ toString id ++ "'");
       pure $ Level.mvar Name.anonymous
  | `Lean.Parser.Level.addLit => do
     level ← toLevel $ stx.getArg 0;
     let k := (stx.getArg 2).toNat;
     pure $ level.addOffset k
  | other => throw "unexpected universe level syntax"

private def setPos (stx : Syntax) (p : PreTerm) : Elab PreTerm :=
if stx.isOfKind `Lean.Parser.Term.app then pure p
else do
  cfg ← read;
  match stx.getPos with
  | none => pure p
  | some pos =>
    let pos := cfg.fileMap.toPosition pos;
    pure $ Expr.mdata ((MData.empty.setNat `column pos.column).setNat `row pos.line) p

def toPreTerm (stx : Syntax) : Elab PreTerm :=
stx.ifNode
  (fun n => do
    s ← get;
    table ← runIO builtinPreTermElabTable.get;
    let k      := n.getKind;
    match table.find k with
    | some fn => fn n >>= setPos stx
    | none    => logErrorAndThrow stx ("`toPreTerm` failed, no support for syntax '" ++ toString k ++ "'"))
  (fun _ => throw "`toPreTerm` failed, unexpected syntax")

@[builtinPreTermElab «type»] def convertType : PreTermElab :=
fun _ => pure $ Expr.sort $ Level.succ Level.zero

@[builtinPreTermElab «sort»] def convertSort : PreTermElab :=
fun _ => pure $ Expr.sort Level.zero

@[builtinPreTermElab «prop»] def convertProp : PreTermElab :=
fun _ => pure $ Expr.sort Level.zero

@[builtinPreTermElab «sortApp»] def convertSortApp : PreTermElab :=
fun n => do
   let sort := n.getArg 0;
   level ← toLevel $ n.getArg 1;
   if sort.isOfKind `Lean.Parser.Term.type then
     pure $ Expr.sort $ Level.succ level
   else
     pure $ Expr.sort level

@[builtinPreTermElab «arrow»] def convertArrow : PreTermElab :=
fun n => do
  id ← mkFreshName;
  dom ← toPreTerm $ n.getArg 0;
  rng ← toPreTerm $ n.getArg 2;
  pure $ Expr.pi id BinderInfo.default dom rng

@[builtinPreTermElab «hole»] def convertHole : PreTermElab :=
fun _ => pure $ Expr.mvar Name.anonymous

@[builtinPreTermElab «sorry»] def convertSorry : PreTermElab :=
fun _ => pure $ Expr.app (Expr.const `sorryAx []) (Expr.mvar Name.anonymous)

end Elab
end Lean
