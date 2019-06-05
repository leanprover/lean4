/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Elaborator for the Lean language: takes commands and produces side effects
-/
prelude
import init.lean.parser.module
import init.lean.expander
import init.lean.expr
import init.lean.options
import init.lean.environment

namespace Lean
-- deprecated Constructor
@[extern "lean_expr_local"]
constant Expr.local (n : Name) (pp : Name) (ty : Expr) (bi : BinderInfo) : Expr := default Expr

namespace Elaborator
-- TODO(Sebastian): move
-- TODO(Sebastian): should be its own Monad?
structure NameGenerator :=
(«prefix» : Name)
(nextIdx : UInt32)

structure SectionVar :=
(uniqName : Name)
(BinderInfo : BinderInfo)
(type : Expr)

/-- Simplified State of the Lean 3 Parser. Maps are replaced with lists for easier interop. -/
structure OldElaboratorState :=
(env : Environment)
(ngen : NameGenerator)
(univs : List (Name × Level))
(vars : List (Name × SectionVar))
(includeVars : List Name)
(Options : Options)
(nextInstIdx : Nat)
(ns : Name)

@[extern "lean_elaborator_elaborate_command"]
constant elaborateCommand (filename : @& String) (e : Expr) (s : @& OldElaboratorState) : Option OldElaboratorState × MessageLog := (none, ⟨[]⟩)

open Parser
open Parser.Combinators
open Parser.Term
open Parser.command
open Parser.command.NotationSpec
open Expander

-- TODO(Sebastian): move
/-- An RBMap that remembers the insertion order. -/
structure OrderedRBMap (α β : Type) (lt : α → α → Bool) :=
(entries : List (α × β))
(map : RBMap α (Nat × β) lt)
(size : Nat)

namespace OrderedRBMap
variables {α β : Type} {lt : α → α → Bool} (m : OrderedRBMap α β lt)

def empty : OrderedRBMap α β lt := {entries := [], map := mkRBMap _ _ _, size := 0}

def insert (k : α) (v : β) : OrderedRBMap α β lt :=
{entries := (k, v)::m.entries, map := m.map.insert k (m.size, v), size := m.size + 1}

def find (a : α) : Option (Nat × β) :=
m.map.find a

def ofList (l : List (α × β)) : OrderedRBMap α β lt :=
l.foldl (λ m p, OrderedRBMap.insert m (Prod.fst p) (Prod.snd p)) OrderedRBMap.empty
end OrderedRBMap

structure ElaboratorConfig extends FrontendConfig :=
(initialParserCfg : ModuleParserConfig)

instance elaboratorConfigCoeFrontendConfig : HasCoe ElaboratorConfig FrontendConfig :=
⟨ElaboratorConfig.toFrontendConfig⟩

/-- Elaborator State that will be reverted at the end of a section or namespace. -/
structure Scope :=
-- "section" or "namespace" (or "MODULE"), currently
(cmd : String)
-- Scope header, should match identifier after `end`. Can be `Name.anonymous` for sections.
(header : Name)
(notations : List NotationMacro := [])
/- The set of local universe variables.
   We remember their insertion order so that we can keep the order when copying them to declarations. -/
(univs : OrderedRBMap Name Level Name.quickLt := OrderedRBMap.empty)
/- The set of local variables. -/
(vars : OrderedRBMap Name SectionVar Name.quickLt := OrderedRBMap.empty)
/- The subset of `vars` that is tagged as always included. -/
(includeVars : RBTree Name Name.quickLt := mkRBTree _ _)
/- The stack of nested active `namespace` commands. -/
(nsStack : List Name := [])
/- The set of active `open` declarations. -/
(openDecls : List openSpec.View := [])
(Options : Options := {})

/-- An `export` command together with the namespace it was declared in. Opening the namespace activates
    the export. -/
structure ScopedExportDecl :=
(inNs : Name)
(spec : openSpec.View)

structure ElaboratorState :=
-- TODO(Sebastian): retrieve from environment
(reservedNotations : List reserveNotation.View := [])
(notations : List NotationMacro := [])
(notationCounter := 0)
/- The current set of `export` declarations (active or inactive). -/
(exportDecls : List ScopedExportDecl := [])

-- Stack of current scopes. The bottom-most Scope is the Module Scope.
(scopes : List Scope)
(messages : MessageLog := MessageLog.empty)
(parserCfg : ModuleParserConfig)
(expanderCfg : Expander.ExpanderConfig)
(env : Environment)
(ngen : NameGenerator)
(nextInstIdx : Nat := 0)

@[derive Monad MonadRec MonadReader MonadState MonadExcept]
def ElaboratorM := RecT Syntax Unit $ ReaderT ElaboratorConfig $ StateT ElaboratorState $ ExceptT Message Id
abbrev Elaborator := Syntax → ElaboratorM Unit

instance elaboratorInh (α : Type) : Inhabited (ElaboratorM α) :=
⟨λ _ _ _, Except.error (default _)⟩

/-- Recursively elaborate any command. -/
def command.elaborate : Elaborator := recurse

def currentScope : ElaboratorM Scope := do
  st ← get,
  match st.scopes with
  | [] := error none "currentScope: unreachable"
  | sc::_ := pure sc

def modifyCurrentScope (f : Scope → Scope) : ElaboratorM Unit := do
  st ← get,
  match st.scopes with
  | [] := error none "modifyCurrentScope: unreachable"
  | sc::scs := set {st with scopes := f sc::scs}

def mangleIdent (id : SyntaxIdent) : Name :=
id.scopes.foldl Name.mkNumeral id.val

partial def levelGetAppArgs : Syntax → ElaboratorM (Syntax × List Syntax)
| stx := do
  match stx.kind with
  | some Level.leading := pure (stx, [])
  | some Level.trailing := match view Level.trailing stx with
    | Level.trailing.View.app lta := do
      (fn, args) ← levelGetAppArgs lta.fn,
      pure (fn, lta.Arg :: args)
    | Level.trailing.View.addLit _ := pure (stx, [])
  | _ := error stx $ "levelGetAppArgs: unexpected input: " ++ toString stx

def levelAdd : Level → Nat → Level
| l 0     := l
| l (n+1) := (levelAdd l n).succ

partial def toLevel : Syntax → ElaboratorM Level
| stx := do
  (fn, args) ← levelGetAppArgs stx,
  sc ← currentScope,
  match fn.kind with
  | some Level.leading := match view Level.leading fn, args with
    | Level.leading.View.hole _, [] := pure $ Level.mvar Name.anonymous
    | Level.leading.View.lit lit, [] := pure $ Level.ofNat lit.toNat
    | Level.leading.View.var id, [] := let id := mangleIdent id in match sc.univs.find id with
      | some _ := pure $ Level.Param id
      | none   := error stx $ "unknown universe variable '" ++ toString id ++ "'"
    | Level.leading.View.max _, (Arg::args) := List.foldr Level.max <$> toLevel Arg <*> args.mmap toLevel
    | Level.leading.View.imax _, (Arg::args) := List.foldr Level.imax <$> toLevel Arg <*> args.mmap toLevel
    | _, _ := error stx "ill-formed universe Level"
  | some Level.trailing := match view Level.trailing fn, args with
    | Level.trailing.View.addLit lta, [] := do
      l ← toLevel lta.lhs,
      pure $ levelAdd l lta.rhs.toNat
    | _, _ := error stx "ill-formed universe Level"
  | _ := error stx $ "toLevel: unexpected input: " ++ toString stx

def Expr.mkAnnotation (ann : Name) (e : Expr) :=
Expr.mdata (MData.empty.setName `annotation ann) e

def dummy : Expr := Expr.const `Prop []

def mkEqns (type : Expr) (eqns : List (Name × List Expr × Expr)): Expr :=
  let eqns := eqns.map $ λ ⟨fn, lhs, rhs⟩, do {
    let fn := Expr.local fn fn type BinderInfo.auxDecl,
    let lhs := Expr.mkApp (Expr.mkAnnotation `@ fn) lhs,
    Expr.app lhs rhs
  } in
  Expr.mkAnnotation `preEquations $ Expr.mkCapp `_ eqns

partial def toPexpr : Syntax → ElaboratorM Expr
| stx@(Syntax.rawNode {kind := k, args := args}) := do
  e ← match k with
  | @identUnivs := do
    let v := view identUnivs stx,
    e ← match v with
    | {id := id, univs := some univs} := Expr.const (mangleIdent id) <$> univs.levels.mmap toLevel
    | {id := id, univs := none}       := pure $ Expr.const (mangleIdent id) [],
    let m := MData.empty.setName `annotation `preresolved,
    let m := v.id.preresolved.enum.foldl (λ (m : MData) ⟨i, n⟩, m.setName (Name.anonymous.mkNumeral i) n) m,
    pure $ Expr.mdata m e
  | @app   := let v := view app stx in
    Expr.app <$> toPexpr v.fn <*> toPexpr v.Arg
  | @lambda := do
    let lam := view lambda stx,
    binders.View.simple bnder ← pure lam.binders
      | error stx "ill-formed lambda",
    (bi, id, type) ← pure bnder.toBinderInfo,
    Expr.lam (mangleIdent id) bi <$> toPexpr type <*> toPexpr lam.body
  | @pi := do
    let v := view pi stx,
    binders.View.simple bnder ← pure v.binders
      | error stx "ill-formed pi",
    (bi, id, type) ← pure bnder.toBinderInfo,
    Expr.pi (mangleIdent id) bi <$> toPexpr type <*> toPexpr v.range
  | @sort := match view sort stx with
    | sort.View.Sort _ := pure $ Expr.sort Level.zero
    | sort.View.Type _ := pure $ Expr.sort $ Level.succ Level.zero
  | @sortApp := do
    let v := view sortApp stx,
    match view sort v.fn with
    | sort.View.Sort _ := Expr.sort <$> toLevel v.Arg
    | sort.View.Type _ := (Expr.sort ∘ Level.succ) <$> toLevel v.Arg
  | @anonymousConstructor := do
    let v := view anonymousConstructor stx,
    p ← toPexpr $ mkApp (review hole {}) (v.args.map SepBy.Elem.View.item),
    pure $ Expr.mkAnnotation `anonymousConstructor p
  | @hole := pure $ Expr.mvar Name.anonymous dummy
  | @«have» := do
    let v := view «have» stx,
    let id := (mangleIdent <$> optIdent.View.id <$> v.id).getOrElse `this,
    let proof := match v.proof with
    | haveProof.View.Term hpt := hpt.Term
    | haveProof.View.from hpf := hpf.from.proof,
    lam ← Expr.lam id BinderInfo.default <$> toPexpr v.prop <*> toPexpr v.body,
    Expr.app (Expr.mkAnnotation `have lam) <$> toPexpr proof
  | @«show» := do
    let v := view «show» stx,
    prop ← toPexpr v.prop,
    proof ← toPexpr v.from.proof,
    pure $ Expr.mkAnnotation `show $ Expr.app (Expr.lam `this BinderInfo.default prop $ Expr.bvar 0) proof
  | @«let» := do
    let v := view «let» stx,
    letLhs.View.id {id := id, binders := [], type := some ty} ← pure v.lhs
      | error stx "ill-formed let",
    Expr.elet (mangleIdent id) <$> toPexpr ty.type <*> toPexpr v.value <*> toPexpr v.body
  | @projection := do
    let v := view projection stx,
    let val := match v.proj with
    | projectionSpec.View.id id := DataValue.ofName id.val
    | projectionSpec.View.num n := DataValue.ofNat n.toNat,
    Expr.mdata (MData.empty.insert `fieldNotation val) <$> toPexpr v.Term
  | @explicit := do
    let v := view explicit stx,
    let ann := match v.mod with
    | explicitModifier.View.explicit _         := `@
    | explicitModifier.View.partialExplicit _ := `@@,
    Expr.mkAnnotation ann <$> toPexpr (review identUnivs v.id)
  | @inaccessible := do
    let v := view inaccessible stx,
    Expr.mkAnnotation `innaccessible <$> toPexpr v.Term  -- sic
  | @borrowed := do
    let v := view borrowed stx,
    Expr.mkAnnotation `borrowed <$> toPexpr v.Term
  | @number := do
    let v := view number stx,
    pure $ Expr.lit $ Literal.natVal v.toNat
  | @stringLit := do
    let v := view stringLit stx,
    pure $ Expr.lit $ Literal.strVal (v.value.getOrElse "NOTAString")
  | @choice := do
    last::rev ← List.reverse <$> args.mmap (λ a, toPexpr a)
      | error stx "ill-formed choice",
    pure $ Expr.mdata (MData.empty.setNat `choice args.length) $
      rev.reverse.foldr Expr.app last
  | @structInst := do
    let v := view structInst stx,
    -- order should be: fields*, sources*, catchall?
    let (fields, other) := v.items.span (λ it, ↑match SepBy.Elem.View.item it with
      | structInstItem.View.field _ := true
      | _ := false),
    let (sources, catchall) := other.span (λ it, ↑match SepBy.Elem.View.item it with
      | structInstItem.View.source {source := some _} := true
      | _ := false),
    catchall ← match catchall with
    | [] := pure false
    | [{item := structInstItem.View.source _}] := pure true
    | {item := it}::_ := error (review structInstItem it) $ "unexpected item in structure instance notation",

    fields ← fields.mmap (λ f, match SepBy.Elem.View.item f with
      | structInstItem.View.field f :=
        Expr.mdata (MData.empty.setName `field $ mangleIdent f.id) <$> toPexpr f.val
      | _ := error stx "toPexpr: unreachable"),
    sources ← sources.mmap (λ src, match SepBy.Elem.View.item src with
      | structInstItem.View.source {source := some src} := toPexpr src
      | _ := error stx "toPexpr: unreachable"),
    sources ← match v.with with
    | none     := pure sources
    | some src := do { src ← toPexpr src.source, pure $ sources ++ [src]},

    let m := MData.empty.setNat "structure instance" fields.length,
    let m := m.setBool `catchall catchall,
    let m := m.setName `struct $
      (mangleIdent <$> structInstType.View.id <$> v.type).getOrElse Name.anonymous,
    let dummy := Expr.sort Level.zero,
    pure $ Expr.mdata m $ (fields ++ sources).foldr Expr.app dummy
  | @«match» := do
    let v := view «match» stx,
    eqns ← (v.equations.map SepBy.Elem.View.item).mmap $ λ (eqn : matchEquation.View), do {
      lhs ← eqn.lhs.mmap $ λ l, toPexpr l.item,
      rhs ← toPexpr eqn.rhs,
      pure (`_matchFn, lhs, rhs)
    },
    type ← toPexpr $ getOptType v.type,
    let eqns := mkEqns type eqns,
    Expr.mdata mdata e ← pure eqns
      | error stx "toPexpr: unreachable",
    let eqns := Expr.mdata (mdata.setBool `match true) e,
    Expr.mkApp eqns <$> v.scrutinees.mmap (λ scr, toPexpr scr.item)
  | _ := error stx $ "toPexpr: unexpected Node: " ++ toString k.name,
  match k with
  | @app := pure e -- no Position
  | _ := do
    cfg ← read,
    match stx.getPos with
    | some pos :=
      let pos := cfg.fileMap.toPosition pos in
      pure $ Expr.mdata ((MData.empty.setNat `column pos.column).setNat `row pos.line) e
    | none := pure e
| stx := error stx $ "toPexpr: unexpected: " ++ toString stx

/-- Returns the active namespace, that is, the concatenation of all active `namespace` commands. -/
def getNamespace : ElaboratorM Name := do
  sc ← currentScope,
  pure $ match sc.nsStack with
  | ns::_ := ns
  | _     := Name.anonymous

def oldElabCommand (stx : Syntax) (cmd : Expr) : ElaboratorM Unit :=
do cfg ← read,
   let pos := cfg.fileMap.toPosition $ stx.getPos.getOrElse (default _),
   let cmd := match cmd with
   | Expr.mdata m e := Expr.mdata ((m.setNat `column pos.column).setNat `row pos.line) e
   | e := e,
   st ← get,
   sc ← currentScope,
   ns ← getNamespace,
   let (st', msgs) := elaborateCommand cfg.filename cmd {
     ns := ns,
     univs := sc.univs.entries.reverse,
     vars := sc.vars.entries.reverse,
     includeVars := sc.includeVars.toList,
     Options := sc.Options,
     ..st},
   match st' with
   | some st' := do modifyCurrentScope $ λ sc, {sc with
       univs := OrderedRBMap.ofList st'.univs,
       vars := OrderedRBMap.ofList st'.vars,
       includeVars := RBTree.ofList st'.includeVars,
       Options := st'.Options,
     },
     modify $ λ st, {..st', ..st}
   | none := pure (),  -- error
   modify $ λ st, {st with messages := st.messages ++ msgs}

def namesToPexpr (ns : List Name) : Expr :=
Expr.mkCapp `_ $ ns.map (λ n, Expr.const n [])

def attrsToPexpr (attrs : List (SepBy.Elem.View attrInstance.View (Option SyntaxAtom))) : ElaboratorM Expr :=
Expr.mkCapp `_ <$> attrs.mmap (λ attr,
  Expr.mkCapp attr.item.Name.val <$> attr.item.args.mmap toPexpr)

def declModifiersToPexpr (mods : declModifiers.View) : ElaboratorM Expr := do
  let mdata : MData := {},
  let mdata := match mods.docComment with
    | some {doc := some doc, ..} := mdata.setString `docString doc.val
    | _ := mdata,
  let mdata := match mods.visibility with
    | some (visibility.View.private _) := mdata.setBool `private true
    | some (visibility.View.protected _) := mdata.setBool `protected true
    | _ := mdata,
  let mdata := mdata.setBool `noncomputable mods.noncomputable.isSome,
  let mdata := mdata.setBool `unsafe mods.unsafe.isSome,
  Expr.mdata mdata <$> attrsToPexpr (match mods.attrs with
    | some attrs := attrs.attrs
    | none       := [])

def identUnivParamsToPexpr (id : identUnivParams.View) : Expr :=
Expr.const (mangleIdent id.id) $ match id.univParams with
  | some params := params.params.map (Level.Param ∘ mangleIdent)
  | none        := []

/-- Execute `elab` and reset local Scope (universes, ...) after it has finished. -/
def locally (elab : ElaboratorM Unit) :
  ElaboratorM Unit := do
  sc ← currentScope,
  elab,
  modifyCurrentScope $ λ _, sc

def simpleBindersToPexpr (bindrs : List simpleBinder.View) : ElaboratorM Expr :=
Expr.mkCapp `_ <$> bindrs.mmap (λ b, do
  let (bi, id, type) := b.toBinderInfo,
  let id := mangleIdent id,
  type ← toPexpr type,
  pure $ Expr.local id id type bi)

def elabDefLike (stx : Syntax) (mods : declModifiers.View) (dl : defLike.View) (kind : Nat) : ElaboratorM Unit :=
match dl with
| {sig := {params := bracketedBinders.View.simple bbs}, ..} := do
  let mdata := MData.empty.setName `command `defs,
  mods ← declModifiersToPexpr mods,
  let kind := Expr.lit $ Literal.natVal kind,
  match dl.oldUnivParams with
  | some uparams :=
    modifyCurrentScope $ λ sc, {sc with univs :=
      (uparams.ids.map mangleIdent).foldl (λ m id, OrderedRBMap.insert m id (Level.Param id)) sc.univs}
  | none := pure (),
  -- do we actually need this??
  let uparams := namesToPexpr $ match dl.oldUnivParams with
  | some uparams := uparams.ids.map mangleIdent
  | none := [],
  let id := mangleIdent dl.Name.id,
  let type := getOptType dl.sig.type,
  type ← toPexpr type,
  let fns := Expr.mkCapp `_ [Expr.local id id type BinderInfo.auxDecl],
  val ← match dl.val with
  | declVal.View.simple val  := toPexpr val.body
  | declVal.View.emptyMatch _ := pure $ mkEqns type []
  | declVal.View.match eqns  := do {
    eqns ← eqns.mmap (λ (eqn : equation.View), do
      lhs ← eqn.lhs.mmap toPexpr,
      rhs ← toPexpr eqn.rhs,
      pure (id, lhs, rhs)
    ),
    pure $ mkEqns type eqns
  },
  params ← simpleBindersToPexpr bbs,
  oldElabCommand stx $ Expr.mdata mdata $ Expr.mkCapp `_ [mods, kind, uparams, fns, params, val]
| _ := error stx "elabDefLike: unexpected input"

def inferModToPexpr (mod : Option inferModifier.View) : Expr :=
Expr.lit $ Literal.natVal $ match mod with
| none := 0
| some $ inferModifier.View.relaxed _ := 1
| some $ inferModifier.View.strict _  := 2

def declaration.elaborate : Elaborator :=
λ stx, locally $ do
  let decl := view «declaration» stx,
  match decl.inner with
  | declaration.inner.View.«axiom» c@{sig := {params := bracketedBinders.View.simple [], type := type}, ..} := do
    let mdata := MData.empty.setName `command `«axiom», -- CommentTo(Kha): It was `constant` here
    mods ← declModifiersToPexpr decl.modifiers,
    let id := identUnivParamsToPexpr c.Name,
    type ← toPexpr type.type,
    oldElabCommand stx $ Expr.mdata mdata $ Expr.mkCapp `_ [mods, id, type]
  | declaration.inner.View.defLike dl := do
      -- The numeric literals below should reflect the enum values
      -- enum class declCmdKind { Theorem, Definition, OpaqueConst, Example, Instance, Var, Abbreviation };
      let kind := match dl.kind with
      | defLike.kind.View.theorem _ := 0
      | defLike.kind.View.def _ := 1
      | defLike.kind.View.«constant» _ := 2
      | defLike.kind.View.abbreviation _ := 6
      | defLike.kind.View.«abbrev» _ := 6,
      elabDefLike stx decl.modifiers dl kind

  -- these are almost macros for `def`, Except the Elaborator handles them specially at a few places
  -- based on the kind
  | declaration.inner.View.example ex :=
    elabDefLike stx decl.modifiers {
      kind := defLike.kind.View.def,
      Name := {id := Name.anonymous},
      sig := {..ex.sig},
      ..ex} 3
  | declaration.inner.View.instance i :=
    elabDefLike stx decl.modifiers {
      kind := defLike.kind.View.def,
      Name := i.Name.getOrElse {id := Name.anonymous},
      sig := {..i.sig},
      ..i} 4

  | declaration.inner.View.inductive ind@{«class» := none, sig := {params := bracketedBinders.View.simple bbs}, ..} := do
    let mdata := MData.empty.setName `command `inductives,
    mods ← declModifiersToPexpr decl.modifiers,
    attrs ← attrsToPexpr (match decl.modifiers.attrs with
      | some attrs := attrs.attrs
      | none       := []),
    let mutAttrs := Expr.mkCapp `_ [attrs],
    match ind.oldUnivParams with
    | some uparams :=
      modifyCurrentScope $ λ sc, {sc with univs :=
        (uparams.ids.map mangleIdent).foldl (λ m id, OrderedRBMap.insert m id (Level.Param id)) sc.univs}
    | none := pure (),
    let uparams := namesToPexpr $ match ind.oldUnivParams with
    | some uparams := uparams.ids.map mangleIdent
    | none := [],
    let id := mangleIdent ind.Name.id,
    let type := getOptType ind.sig.type,
    type ← toPexpr type,
    let indL := Expr.local id id type BinderInfo.default,
    let inds := Expr.mkCapp `_ [indL],
    params ← simpleBindersToPexpr bbs,
    introRules ← ind.introRules.mmap (λ (r : introRule.View), do
      ({params := bracketedBinders.View.simple [], type := some ty}) ← pure r.sig
        | error stx "declaration.elaborate: unexpected input",
      type ← toPexpr ty.type,
      let Name := mangleIdent r.Name,
      pure $ Expr.local Name Name type BinderInfo.default),
    let introRules := Expr.mkCapp `_ introRules,
    let introRules := Expr.mkCapp `_ [introRules],
    let inferKinds := ind.introRules.map $ λ (r : introRule.View), inferModToPexpr r.inferMod,
    let inferKinds := Expr.mkCapp `_ inferKinds,
    let inferKinds := Expr.mkCapp `_ [inferKinds],
    oldElabCommand stx $ Expr.mdata mdata $
      Expr.mkCapp `_ [mods, mutAttrs, uparams, inds, params, introRules, inferKinds]

  | declaration.inner.View.structure s@{keyword := structureKw.View.structure _, sig := {params := bracketedBinders.View.simple bbs}, ..} := do
    let mdata := MData.empty.setName `command `structure,
    mods ← declModifiersToPexpr decl.modifiers,
    match s.oldUnivParams with
    | some uparams :=
      modifyCurrentScope $ λ sc, {sc with univs :=
        (uparams.ids.map mangleIdent).foldl (λ m id, OrderedRBMap.insert m id (Level.Param id)) sc.univs}
    | none := pure (),
    let uparams := namesToPexpr $ match s.oldUnivParams with
    | some uparams := uparams.ids.map mangleIdent
    | none := [],
    let Name := mangleIdent s.Name.id,
    let Name := Expr.local Name Name dummy BinderInfo.default,
    let type := getOptType s.sig.type,
    type ← toPexpr type,
    params ← simpleBindersToPexpr bbs,
    let parents := match s.extends with
    | some ex := ex.parents
    | none    := [],
    parents ← parents.mmap (toPexpr ∘ SepBy.Elem.View.item),
    let parents := Expr.mkCapp `_ parents,
    let mk := match s.ctor with
    | some ctor := mangleIdent ctor.Name
    | none      := `mk,
    let mk := Expr.local mk mk dummy BinderInfo.default,
    let infer := inferModToPexpr (s.ctor >>= structureCtor.View.inferMod),
    fieldBlocks ← s.fieldBlocks.mmap (λ bl, do
      (bi, content) ← match bl with
        | structureFieldBlock.View.explicit {content := structExplicitBinderContent.View.notation _} :=
          error stx "declaration.elaborate: unexpected input"
        | structureFieldBlock.View.explicit {content := structExplicitBinderContent.View.other c} :=
          pure (BinderInfo.default, c)
        | structureFieldBlock.View.implicit {content := c} := pure (BinderInfo.implicit, c)
        | structureFieldBlock.View.strictImplicit {content := c} := pure (BinderInfo.strictImplicit, c)
        | structureFieldBlock.View.instImplicit {content := c} := pure (BinderInfo.instImplicit, c),
      let bi := Expr.local `_ `_ dummy bi,
      let ids := namesToPexpr $ content.ids.map mangleIdent,
      let kind := inferModToPexpr content.inferMod,
      let type := getOptType content.sig.type,
      type ← toPexpr type,
      pure $ Expr.mkCapp `_ [bi, ids, kind, type]),
    let fieldBlocks := Expr.mkCapp `_ fieldBlocks,
    oldElabCommand stx $ Expr.mdata mdata $
      Expr.mkCapp `_ [mods, uparams, Name, params, parents, type, mk, infer, fieldBlocks]
  | _ :=
    error stx "declaration.elaborate: unexpected input"

def variables.elaborate : Elaborator :=
λ stx, do
  let mdata := MData.empty.setName `command `variables,
  let v := view «variables» stx,
  vars ← match v.binders with
  | bracketedBinders.View.simple bbs := bbs.mfilter $ λ b, do
    let (bi, id, type) := b.toBinderInfo,
    if type.isOfKind bindingAnnotationUpdate then do
      sc ← currentScope,
      let id := mangleIdent id,
      match sc.vars.find id with
      | some (_, v) :=
        modifyCurrentScope $ λ sc, {sc with vars :=
          sc.vars.insert id {v with BinderInfo := bi}}
      | none := error (Syntax.ident id) "",
      pure false
    else pure true
  | _ := error stx "variables.elaborate: unexpected input",
  vars ← simpleBindersToPexpr vars,
  oldElabCommand stx $ Expr.mdata mdata vars

def include.elaborate : Elaborator :=
λ stx, do
  let v := view «include» stx,
  -- TODO(Sebastian): error checking
  modifyCurrentScope $ λ sc, {sc with includeVars :=
    v.ids.foldl (λ vars v, vars.insert $ mangleIdent v) sc.includeVars}

-- TODO: RBMap.remove
/-
def omit.elaborate : Elaborator :=
λ stx, do
  let v := View «omit» stx,
  modify $ λ st, {st with localState := {sc with includeVars :=
    v.ids.foldl (λ vars v, vars.remove $ mangleIdent v) sc.includeVars}}
-/

def Module.header.elaborate : Elaborator :=
λ stx, do
  let header := view Module.header stx,
  match header with
  | {«prelude» := some _, imports := []} := pure ()
  | _ := error stx "not implemented: imports"

def precToNat : Option precedence.View → Nat
| (some prec) := prec.Term.toNat
| none        := 0

-- TODO(Sebastian): Command parsers like `structure` will need access to these
def CommandParserConfig.registerNotationTokens (spec : NotationSpec.View) (cfg : CommandParserConfig) :
  Except String CommandParserConfig :=
do spec.rules.mfoldl (λ (cfg : CommandParserConfig) r, match r.symbol with
   | notationSymbol.View.quoted {symbol := some a, prec := prec, ..} :=
     pure {cfg with tokens := cfg.tokens.insert a.val.trim {«prefix» := a.val.trim, lbp := precToNat prec}}
   | _ := throw "registerNotationTokens: unreachable") cfg

def CommandParserConfig.registerNotationParser (k : SyntaxNodeKind) (nota : notation.View)
  (cfg : CommandParserConfig) : Except String CommandParserConfig :=
do -- build and register Parser
   ps ← nota.spec.rules.mmap (λ r : rule.View, do
     psym ← match r.symbol with
     | notationSymbol.View.quoted {symbol := some a ..} :=
       pure (symbol a.val : termParser)
     | _ := throw "registerNotationParser: unreachable",
     ptrans ← match r.transition with
     | some (transition.View.binder b) :=
       pure $ some $ Term.binderIdent.Parser
     | some (transition.View.binders b) :=
       pure $ some $ Term.binders.Parser
     | some (transition.View.Arg {action := none, ..}) :=
       pure $ some Term.Parser
     | some (transition.View.Arg {action := some {kind := actionKind.View.prec prec}, ..}) :=
       pure $ some $ Term.Parser prec.toNat
     | some (transition.View.Arg {action := some {kind := actionKind.View.scoped sc}, ..}) :=
       pure $ some $ Term.Parser $ precToNat sc.prec
     | none := pure $ none
     | _ := throw "registerNotationParser: unimplemented",
     pure $ psym::ptrans.toMonad
   ),
   firstRule::_ ← pure nota.spec.rules | throw "registerNotationParser: unreachable",
   firstTk ← match firstRule.symbol with
   | notationSymbol.View.quoted {symbol := some a ..} :=
     pure a.val.trim
   | _ := throw "registerNotationParser: unreachable",
   let ps := ps.bind id,
   cfg ← match nota.local, nota.spec.prefixArg with
   | none,   none   := pure {cfg with leadingTermParsers :=
     cfg.leadingTermParsers.insert firstTk $ Parser.Combinators.node k ps}
   | some _, none   := pure {cfg with localLeadingTermParsers :=
     cfg.localLeadingTermParsers.insert firstTk $ Parser.Combinators.node k ps}
   | none,   some _ := pure {cfg with trailingTermParsers :=
     cfg.trailingTermParsers.insert firstTk $ Parser.Combinators.node k (getLeading::ps.map coe)}
   | some _, some _ := pure {cfg with localTrailingTermParsers :=
     cfg.localTrailingTermParsers.insert firstTk $ Parser.Combinators.node k (getLeading::ps.map coe)},
   pure cfg

/-- Recreate `ElaboratorState.parserCfg` from the Elaborator State and the initial config,
    effectively treating it as a cache. -/
def updateParserConfig : ElaboratorM Unit :=
do st ← get,
   sc ← currentScope,
   cfg ← read,
   let ccfg := cfg.initialParserCfg.toCommandParserConfig,
   ccfg ← st.reservedNotations.mfoldl (λ ccfg rnota,
     match CommandParserConfig.registerNotationTokens rnota.spec ccfg with
     | Except.ok ccfg := pure ccfg
     | Except.error e := error (review reserveNotation rnota) e) ccfg,
   ccfg ← (st.notations ++ sc.notations).mfoldl (λ ccfg nota,
     match CommandParserConfig.registerNotationTokens nota.nota.spec ccfg >>=
               CommandParserConfig.registerNotationParser nota.kind nota.nota with
     | Except.ok ccfg := pure ccfg
     | Except.error e := error (review «notation» nota.nota) e) ccfg,
   set {st with parserCfg := {cfg.initialParserCfg with toCommandParserConfig := ccfg}}

def postprocessNotationSpec (spec : NotationSpec.View) : NotationSpec.View :=
-- default leading tokens to `max`
-- NOTE: should happen after copying precedences from reserved notation
match spec with
| {prefixArg := none, rules := r@{symbol := notationSymbol.View.quoted sym@{prec := none, ..}, ..}::rs} :=
  {spec with rules := {r with symbol := notationSymbol.View.quoted {sym with prec := some
    {Term := precedenceTerm.View.lit $ precedenceLit.View.num $ number.View.ofNat maxPrec}
  }}::rs}
| _ := spec

def reserveNotation.elaborate : Elaborator :=
λ stx, do
  let v := view reserveNotation stx,
  let v := {v with spec := postprocessNotationSpec v.spec},
  -- TODO: sanity checks?
  modify $ λ st, {st with reservedNotations := v::st.reservedNotations},
  updateParserConfig

def matchPrecedence : Option precedence.View → Option precedence.View → Bool
| none      (some rp) := true
| (some sp) (some rp) := sp.Term.toNat = rp.Term.toNat
| _         _         := false

/-- Check if a notation is compatible with a reserved notation, and if so, copy missing
    precedences in the notation from the reserved notation. -/
def matchSpec (spec reserved : NotationSpec.View) : Option NotationSpec.View :=
do guard $ spec.prefixArg.isSome = reserved.prefixArg.isSome,
   rules ← (spec.rules.zip reserved.rules).mmap $ λ ⟨sr, rr⟩, do {
     notationSymbol.View.quoted sq@{symbol := some sa, ..} ← pure sr.symbol
       | failure,
     notationSymbol.View.quoted rq@{symbol := some ra, ..} ← pure rr.symbol
       | failure,
     guard $ sa.val.trim = ra.val.trim,
     guard $ matchPrecedence sq.prec rq.prec,
     st ← match sr.transition, rr.transition with
     | some (transition.View.binder sb), some (transition.View.binder rb) :=
       guard (matchPrecedence sb.prec rb.prec) *> pure rr.transition
     | some (transition.View.binders sb), some (transition.View.binders rb) :=
       guard (matchPrecedence sb.prec rb.prec) *> pure rr.transition
     | some (transition.View.Arg sarg), some (transition.View.Arg rarg) := do
       sact ← match action.View.kind <$> sarg.action, action.View.kind <$> rarg.action with
       | some (actionKind.View.prec sp), some (actionKind.View.prec rp) :=
         guard (sp.toNat = rp.toNat) *> pure sarg.action
       | none,                            some (actionKind.View.prec rp) :=
         pure rarg.action
       | _, _ := failure,
       pure $ some $ transition.View.Arg {sarg with action := sact}
     | none,    none    := pure none
     | _,       _       := failure,
     pure $ {rule.View .
       symbol := notationSymbol.View.quoted rq,
       transition := st}
   },
   pure $ {spec with rules := rules}

def notation.elaborateAux : notation.View → ElaboratorM notation.View :=
λ nota, do
  st ← get,
  -- check reserved notations
  matched ← pure $ st.reservedNotations.filterMap $
    λ rnota, matchSpec nota.spec rnota.spec,
  nota ← match matched with
  | [matched] := pure {nota with spec := matched}
  | []        := pure nota
  | _         := error (review «notation» nota) "invalid notation, matches multiple reserved notations",
  -- TODO: sanity checks
  pure {nota with spec := postprocessNotationSpec nota.spec}

-- TODO(Sebastian): better kind names, Module prefix?
def mkNotationKind : ElaboratorM SyntaxNodeKind :=
do st ← get,
   set {st with notationCounter := st.notationCounter + 1},
   pure {name := (`_notation).mkNumeral st.notationCounter}

/-- Register a notation in the Expander. Unlike with notation parsers, there is no harm in
    keeping local notation macros registered after closing a section. -/
def registerNotationMacro (nota : notation.View) : ElaboratorM NotationMacro :=
do k ← mkNotationKind,
   let m : NotationMacro := ⟨k, nota⟩,
   let transf := mkNotationTransformer m,
   modify $ λ st, {st with expanderCfg := {st.expanderCfg with transformers := st.expanderCfg.transformers.insert k.name transf}},
   pure m

def notation.elaborate : Elaborator :=
λ stx, do
  let nota := view «notation» stx,
  -- HACK: ignore List Literal notation using :fold
  let usesFold := nota.spec.rules.any $ λ r, match r.transition with
    | some (transition.View.Arg {action := some {kind := actionKind.View.fold _, ..}, ..}) := true
    | _ := false,
  if usesFold then do {
    cfg ← read,
    modify $ λ st, {st with messages := st.messages.add {filename := cfg.filename, pos := ⟨1,0⟩,
      severity := MessageSeverity.warning, text := "ignoring notation using 'fold' action"}}
  } else do {
    nota ← notation.elaborateAux nota,
    m ← registerNotationMacro nota,
    match nota.local with
      | some _ := modifyCurrentScope $ λ sc, {sc with notations := m::sc.notations}
      | none   := modify $ λ st, {st with notations := m::st.notations},
    updateParserConfig
  }

def universe.elaborate : Elaborator :=
λ stx, do
  let univ := view «universe» stx,
  let id := mangleIdent univ.id,
  sc ← currentScope,
  match sc.univs.find id with
  | none   := modifyCurrentScope $ λ sc, {sc with univs := sc.univs.insert id (Level.Param id)}
  | some _ := error stx $ "a universe named '" ++ toString id ++ "' has already been declared in this Scope"

def attribute.elaborate : Elaborator :=
λ stx, do
  let attr := view «attribute» stx,
  let mdata := MData.empty.setName `command `attribute,
  let mdata := mdata.setBool `local $ attr.local.isSome,
  attrs ← attrsToPexpr attr.attrs,
  ids ← attr.ids.mmap (λ id, match id.preresolved with
    | []  := error (Syntax.ident id) $ "unknown identifier '" ++ toString id.val ++ "'"
    | [c] := pure $ Expr.const c []
    | _   := error (Syntax.ident id) "invalid 'attribute' command, identifier is ambiguous"),
  let ids := Expr.mkCapp `_ ids,
  oldElabCommand stx $ Expr.mdata mdata $ Expr.app attrs ids

def check.elaborate : Elaborator :=
λ stx, do
  let v := view check stx,
  let mdata := MData.empty.setName `command `#check,
  e ← toPexpr v.Term,
  oldElabCommand stx $ Expr.mdata mdata e

def open.elaborate : Elaborator :=
λ stx, do
  let v := view «open» stx,
  -- TODO: do eager sanity checks (namespace does not exist, etc.)
  modifyCurrentScope $ λ sc, {sc with openDecls := sc.openDecls ++ v.spec}

def export.elaborate : Elaborator :=
λ stx, do
  let v := view «export» stx,
  ns ← getNamespace,
  -- TODO: do eager sanity checks (namespace does not exist, etc.)
  modify $ λ st, {st with exportDecls := st.exportDecls ++ v.spec.map (λ spec, ⟨ns, spec⟩)}

def initQuot.elaborate : Elaborator :=
λ stx, oldElabCommand stx $ Expr.mdata (MData.empty.setName `command `initQuot) dummy

def setOption.elaborate : Elaborator :=
λ stx, do
  let v := view «setOption» stx,
  let opt := v.opt.val,
  sc ← currentScope,
  let opts := sc.Options,
  -- TODO(Sebastian): check registered Options
  let opts := match v.val with
  | optionValue.View.Bool b := opts.setBool opt (match b with boolOptionValue.View.True _ := true | _ := false)
  | optionValue.View.String lit := match lit.value with
    | some s := opts.setString opt s
    | none   := opts  -- Parser already failed
  | optionValue.View.num lit := opts.setNat opt lit.toNat,
  modifyCurrentScope $ λ sc, {sc with Options := opts}

/-- List of commands: recursively elaborate each command. -/
def noKind.elaborate : Elaborator := λ stx, do
  some n ← pure stx.asNode
    | error stx "noKind.elaborate: unreachable",
  n.args.mfor command.elaborate

def end.elaborate : Elaborator :=
λ cmd, do
  let v := view «end» cmd,
  st ← get,
  -- NOTE: bottom-most (Module) Scope cannot be closed
  sc::sc'::scps ← pure st.scopes
    | error cmd "invalid 'end', there is no open Scope to end",
  let endName := mangleIdent $ v.Name.getOrElse Name.anonymous,
  when (endName ≠ sc.header) $
    error cmd $ "invalid end of " ++ sc.cmd ++ ", expected Name '" ++
      toString sc.header ++ "'",
  set {st with scopes := sc'::scps},
  -- local notations may have vanished
  updateParserConfig

def section.elaborate : Elaborator :=
λ cmd, do
  let sec := view «section» cmd,
  let header := mangleIdent $ sec.Name.getOrElse Name.anonymous,
  sc ← currentScope,
  modify $ λ st, {st with scopes := {sc with cmd := "section", header := header}::st.scopes}

def namespace.elaborate : Elaborator :=
λ cmd, do
  let v := view «namespace» cmd,
  let header := mangleIdent v.Name,
  sc ← currentScope,
  ns ← getNamespace,
  let sc' := {sc with cmd := "namespace", header := header, nsStack := (ns ++ header)::sc.nsStack},
  modify $ λ st, {st with scopes := sc'::st.scopes}

def eoi.elaborate : Elaborator :=
λ cmd, do
  st ← get,
  when (st.scopes.length > 1) $
    error cmd "invalid end of input, expected 'end'"

-- TODO(Sebastian): replace with attribute
def elaborators : RBMap Name Elaborator Name.quickLt := RBMap.fromList [
  (Module.header.name, Module.header.elaborate),
  (notation.name, notation.elaborate),
  (reserveNotation.name, reserveNotation.elaborate),
  (universe.name, universe.elaborate),
  (noKind.name, noKind.elaborate),
  (end.name, end.elaborate),
  (section.name, section.elaborate),
  (namespace.name, namespace.elaborate),
  (variables.name, variables.elaborate),
  (include.name, include.elaborate),
  --(omit.name, omit.elaborate),
  (declaration.name, declaration.elaborate),
  (attribute.name, attribute.elaborate),
  (open.name, open.elaborate),
  (export.name, export.elaborate),
  (check.name, check.elaborate),
  (initQuot.name, initQuot.elaborate),
  (setOption.name, setOption.elaborate),
  (Module.eoi.name, eoi.elaborate)
] _

-- TODO: optimize
def isOpenNamespace (sc : Scope) : Name → Bool
| Name.anonymous := true
| ns :=
  -- check surrounding namespaces
  ns ∈ sc.nsStack ∨
  -- check opened namespaces
  sc.openDecls.any (λ od, od.id.val = ns) ∨
  -- TODO: check active exports
  false

-- TODO: `hiding`, `as`, `renaming`
def matchOpenSpec (n : Name) (spec : openSpec.View) : Option Name :=
let matchesOnly := match spec.only with
| none := true
| some only := n = only.id.val ∨ only.ids.any (λ id, n = id.val) in
if matchesOnly then some (spec.id.val ++ n) else none

def resolveContext : Name → ElaboratorM (List Name)
| n := do
  st ← get,
  sc ← currentScope, pure $

  -- TODO(Sebastian): check the interaction betwen preresolution and section variables
  match sc.vars.find n with
  | some (_, v) := [v.uniqName]
  | _ :=

  -- global resolution

  -- check surrounding namespaces first
  -- TODO: check for `protected`
  match sc.nsStack.filter (λ ns, st.env.contains (ns ++ n)) with
  | ns::_ := [ns ++ n] -- prefer innermost namespace
  | _ :=

  -- check environment directly
  (let unrooted := n.replacePrefix `_root_ Name.anonymous in
   match st.env.contains unrooted with
   | true := [unrooted]
   | _ := [])
  ++
  -- check opened namespaces
  (let ns' := sc.openDecls.filterMap (matchOpenSpec n) in
   ns'.filter (λ n', st.env.contains n'))
  ++
  -- check active exports
  -- TODO: optimize
  -- TODO: Lean 3 activates an export in `foo` even on `open foo (specificThing)`, but does that make sense?
  (let eds' := st.exportDecls.filter (λ ed, isOpenNamespace sc ed.inNs) in
   let ns' := eds'.filterMap (λ ed, matchOpenSpec n ed.spec) in
   ns'.filter (λ n', st.env.contains n'))

  -- TODO: projection notation

partial def preresolve : Syntax → ElaboratorM Syntax
| (Syntax.ident id) := do
  let n := mangleIdent id,
  ns ← resolveContext n,
  pure $ Syntax.ident {id with preresolved := ns ++ id.preresolved}
| (Syntax.rawNode n) := do
  args ← n.args.mmap preresolve,
  pure $ Syntax.rawNode {n with args := args}
| stx := pure stx

def mkState (cfg : ElaboratorConfig) (env : Environment) (opts : Options) : ElaboratorState := {
  parserCfg := cfg.initialParserCfg,
  expanderCfg := {transformers := Expander.builtinTransformers, ..cfg},
  env := env,
  ngen := ⟨`_ngen.fixme, 0⟩,
  scopes := [{cmd := "MODULE", header := `MODULE, Options := opts}]}

def processCommand (cfg : ElaboratorConfig) (st : ElaboratorState) (cmd : Syntax) : ElaboratorState :=
let st := {st with messages := MessageLog.empty} in
let r := @ExceptT.run _ Id _ $ flip StateT.run st $ flip ReaderT.run cfg $ RecT.run
  (command.elaborate cmd)
  (λ _, error cmd "Elaborator.run: recursion depth exceeded")
  (λ cmd, do
    some n ← pure cmd.asNode |
      error cmd $ "not a command: " ++ toString cmd,
    some elab ← pure $ elaborators.find n.kind.name |
      error cmd $ "unknown command: " ++ toString n.kind.name,
    cmd' ← preresolve cmd,
    elab cmd') in
match r with
| Except.ok ((), st) := st
| Except.error e     := {st with messages := st.messages.add e}

end Elaborator
end Lean
