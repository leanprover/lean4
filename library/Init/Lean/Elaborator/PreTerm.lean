/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Elaborator.Basic

namespace Lean

abbrev PreTerm := Expr

@[extern "lean_old_elaborate"]
constant oldElaborateAux : Environment → Options → MetavarContext → LocalContext → PreTerm → Except (Option Position × Format) (Environment × MetavarContext × Expr) := default _

abbrev PreTermElab := SyntaxNode Expr → Elab PreTerm

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

def mkAsIs (e : Expr) : PreTerm :=
e.mkAnnotation `as_is

def mkAsPattern (id : Name) (e : PreTerm) : PreTerm :=
(Expr.app (Expr.fvar id) e).mkAnnotation `as_pattern

def mkPreTypeAscription (p : PreTerm) (expectedType : Expr) : PreTerm :=
Expr.app (Expr.app (Expr.const `typedExpr []) expectedType) p

def mkPreTypeAscriptionIfSome (p : PreTerm) (expectedType : Option Expr) : PreTerm :=
match expectedType with
| none => p
| some expectedType => mkPreTypeAscription p expectedType

namespace Elab

partial def toLevel : Syntax Expr → Elab Level
| stx => do
  match stx.getKind with
  | `Lean.Parser.Level.paren  => toLevel $ stx.getArg 1
  | `Lean.Parser.Level.max    => do
     let args := (stx.getArg 1).getArgs;
     first ← toLevel (args.get! 0);
     args.foldlFromM (fun r arg => Level.max r <$> toLevel arg) first 1
  | `Lean.Parser.Level.imax   => do
     let args := (stx.getArg 1).getArgs;
     first ← toLevel (args.get! 0);
     args.foldlFromM (fun r arg => Level.imax r <$> toLevel arg) first 1
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

private def setPos (stx : Syntax Expr) (p : PreTerm) : Elab PreTerm :=
if stx.isOfKind `Lean.Parser.Term.app then pure p
else do
  cfg ← read;
  match stx.getPos with
  | none => pure p
  | some pos =>
    let pos := cfg.fileMap.toPosition pos;
    pure $ Expr.mdata ((MData.empty.setNat `column pos.column).setNat `row pos.line) p

def toPreTerm (stx : Syntax Expr) : Elab PreTerm :=
stx.ifNode
  (fun n => do
    s ← get;
    table ← runIO builtinPreTermElabTable.get;
    let k      := n.getKind;
    match table.find k with
    | some fn => fn n >>= setPos stx
    | none    => logErrorAndThrow stx ("`toPreTerm` failed, no support for syntax '" ++ toString k ++ "'"))
  (fun _ => throw "`toPreTerm` failed, unexpected syntax")

private def mkHoleFor (stx : Syntax Expr) : Elab PreTerm :=
setPos stx (Expr.mvar Name.anonymous)

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

private def mkLocal (decl : LocalDecl) : PreTerm :=
Expr.local decl.name decl.userName decl.type decl.binderInfo

private def processBinder (b : Syntax Expr) : Elab (Array PreTerm) :=
match b.getKind with
| `Lean.Parser.Term.simpleBinder   => do
   let args := (b.getArg 0).getArgs;
   args.mapM $ fun arg => do
     let id := arg.getId;
     hole ← mkHoleFor arg;
     -- decl ← mkLocalDecl id hole;  -- HACK: this file will be deleted
     -- pure (mkLocal decl)
     mkLocalDecl id hole
| `Lean.Parser.Term.explicitBinder =>
   let ids     := (b.getArg 1).getArgs;
   let optType := b.getArg 2;
   let optDef  := b.getArg 3;
   ids.mapM $ fun idStx => do
     let id := idStx.getId;
     type ← if optType.getNumArgs == 0 then mkHoleFor idStx else toPreTerm (optType.getArg 1);
     type ← if optDef.getNumArgs == 0 then pure type else
       let defInfo := optDef.getArg 0;
       match defInfo.getKind with
       | `Lean.Parser.Term.binderDefault => do
          defVal ← toPreTerm (defInfo.getArg 1);
          pure $ Expr.app (Expr.app (Expr.const `optParam []) type) defVal
       | `Lean.Parser.Term.binderTactic => logErrorAndThrow optDef "old elaborator does not support tactics in parameters"
       | _ => throw "unknown binder default value annotation";
     -- decl ← mkLocalDecl id type;   -- HACK: this file will be deleted
     -- pure (mkLocal decl)
     mkLocalDecl id type
| `Lean.Parser.Term.implicitBinder => do runIO (IO.println $ ">> implict " ++ (toString b)); pure #[]
| `Lean.Parser.Term.instBinder     => do runIO (IO.println $ ">> inst " ++ (toString b)); pure #[]
| _ => throw "unknown binder kind"

private def processBinders (bs : Array (Syntax Expr)) : Elab (Array PreTerm) :=
bs.foldlM (fun r s => do xs ← processBinder s; pure (r ++ xs)) #[]

@[builtinPreTermElab «forall»] def convertForall : PreTermElab :=
fun n => do
  let binders := n.getArg 1;
  let body    := n.getArg 3;
  withNewScope $ do
    xs   ← processBinders binders.getArgs;
    body ← toPreTerm body;
    mkForall xs body

@[builtinPreTermElab «hole»] def convertHole : PreTermElab :=
fun _ => pure $ Expr.mvar Name.anonymous

@[builtinPreTermElab «sorry»] def convertSorry : PreTermElab :=
fun _ => pure $ Expr.app (Expr.const `sorryAx []) (Expr.mvar Name.anonymous)

@[builtinPreTermElab «id»] def convertId : PreTermElab :=
fun n => do
  let id := n.getIdAt 0;
  -- TODO add support for `explicitUniv` and `namedPattern`
  lctx ← localContext;
  match lctx.findFromUserName id with
  | some decl => pure $ mkLocal decl
  | none =>
    -- TODO global name resolution
    logErrorAndThrow n.val ("unknown identifier '" ++ toString id ++ "'")

def oldElaborate (stx : Syntax Expr) (expectedType : Option Expr := none) : Elab Expr :=
do p ← toPreTerm stx;
   scope ← getScope;
   s ← get;
   match oldElaborateAux s.env scope.options s.mctx scope.lctx (mkPreTypeAscriptionIfSome p expectedType) with
     | Except.error (some pos, fmt) => do
       ctx ← read;
       logMessage { fileName := ctx.fileName, pos := pos, data := MessageData.ofFormat fmt };
       throw ElabException.silent
     | Except.error (none, fmt)     => logErrorAndThrow stx (fmt.pretty scope.options)
     | Except.ok (env, mctx, e)     => do
       modify $ fun s => { env := env, mctx := mctx, .. s };
       pure e

end Elab
end Lean
