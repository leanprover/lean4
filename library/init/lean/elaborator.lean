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

namespace lean
-- TODO(Sebastian): should probably be meta together with the whole elaborator
constant environment : Type := unit

@[extern "leanEnvironmentContains"]
constant environment.contains (env : @& environment) (n : @& name) : bool := ff
-- deprecated constructor
@[extern "leanExprLocal"]
constant expr.local (n : name) (pp : name) (ty : expr) (bi : binderInfo) : expr := default expr

namespace elaborator
-- TODO(Sebastian): move
-- TODO(Sebastian): should be its own monad?
structure nameGenerator :=
(«prefix» : name)
(nextIdx : uint32)

structure sectionVar :=
(uniqName : name)
(binderInfo : binderInfo)
(type : expr)

/-- Simplified state of the Lean 3 parser. Maps are replaced with lists for easier interop. -/
structure oldElaboratorState :=
(env : environment)
(ngen : nameGenerator)
(univs : list (name × level))
(vars : list (name × sectionVar))
(includeVars : list name)
(options : options)
(nextInstIdx : nat)
(ns : name)

@[extern "leanElaboratorElaborateCommand"]
constant elaborateCommand (filename : @& string) (e : expr) (s : @& oldElaboratorState) : option oldElaboratorState × messageLog := (none, ⟨[]⟩)

open parser
open parser.combinators
open parser.term
open parser.command
open parser.command.notationSpec
open expander

local attribute [instance] name.hasLtQuick

-- TODO(Sebastian): move
/-- An rbmap that remembers the insertion order. -/
structure orderedRbmap (α β : Type) (lt : α → α → Prop) :=
(entries : list (α × β))
(map : rbmap α (nat × β) lt)
(size : nat)

namespace orderedRbmap
variables {α β : Type} {lt : α → α → Prop} [decidableRel lt] (m : orderedRbmap α β lt)

def empty : orderedRbmap α β lt := {entries := [], map := mkRbmap _ _ _, size := 0}

def insert (k : α) (v : β) : orderedRbmap α β lt :=
{entries := (k, v)::m.entries, map := m.map.insert k (m.size, v), size := m.size + 1}

def find (a : α) : option (nat × β) :=
m.map.find a

def ofList (l : list (α × β)) : orderedRbmap α β lt :=
l.foldl (λ m p, orderedRbmap.insert m (prod.fst p) (prod.snd p)) orderedRbmap.empty
end orderedRbmap

structure elaboratorConfig extends frontendConfig :=
(initialParserCfg : moduleParserConfig)

instance elaboratorConfigCoeFrontendConfig : hasCoe elaboratorConfig frontendConfig :=
⟨elaboratorConfig.toFrontendConfig⟩

/-- Elaborator state that will be reverted at the end of a section or namespace. -/
structure scope :=
-- "section" or "namespace" (or "MODULE"), currently
(cmd : string)
-- Scope header, should match identifier after `end`. Can be `name.anonymous` for sections.
(header : name)
(notations : list notationMacro := [])
/- The set of local universe variables.
   We remember their insertion order so that we can keep the order when copying them to declarations. -/
(univs : orderedRbmap name level (<) := orderedRbmap.empty)
/- The set of local variables. -/
(vars : orderedRbmap name sectionVar (<) := orderedRbmap.empty)
/- The subset of `vars` that is tagged as always included. -/
(includeVars : rbtree name (<) := mkRbtree _ _)
/- The stack of nested active `namespace` commands. -/
(nsStack : list name := [])
/- The set of active `open` declarations. -/
(openDecls : list openSpec.view := [])
(options : options := options.mk)

/-- An `export` command together with the namespace it was declared in. Opening the namespace activates
    the export. -/
structure scopedExportDecl :=
(inNs : name)
(spec : openSpec.view)

structure elaboratorState :=
-- TODO(Sebastian): retrieve from environment
(reservedNotations : list reserveNotation.view := [])
(notations : list notationMacro := [])
(notationCounter := 0)
/- The current set of `export` declarations (active or inactive). -/
(exportDecls : list scopedExportDecl := [])

-- Stack of current scopes. The bottom-most scope is the module scope.
(scopes : list scope)
(messages : messageLog := messageLog.empty)
(parserCfg : moduleParserConfig)
(expanderCfg : expander.expanderConfig)
(env : environment)
(ngen : nameGenerator)
(nextInstIdx : nat := 0)

@[derive monad monadRec monadReader monadState monadExcept]
def elaboratorM := recT syntax unit $ readerT elaboratorConfig $ stateT elaboratorState $ exceptT message id
abbrev elaborator := syntax → elaboratorM unit

/-- Recursively elaborate any command. -/
def command.elaborate : elaborator := recurse

def currentScope : elaboratorM scope := do
  st ← get,
  match st.scopes with
  | [] := error none "currentScope: unreachable"
  | sc::_ := pure sc

def modifyCurrentScope (f : scope → scope) : elaboratorM unit := do
  st ← get,
  match st.scopes with
  | [] := error none "modifyCurrentScope: unreachable"
  | sc::scs := put {st with scopes := f sc::scs}

def mangleIdent (id : syntaxIdent) : name :=
id.scopes.foldl name.mkNumeral id.val

def levelGetAppArgs : syntax → elaboratorM (syntax × list syntax)
| stx := do
  match stx.kind with
  | some level.leading := pure (stx, [])
  | some level.trailing := (match view level.trailing stx with
    | level.trailing.view.app lta := do
      (fn, args) ← levelGetAppArgs lta.fn,
      pure (fn, lta.arg :: args)
    | level.trailing.view.addLit _ := pure (stx, []))
  | _ := error stx $ "levelGetAppArgs: unexpected input: " ++ toString stx

def levelAdd : level → nat → level
| l 0     := l
| l (n+1) := (levelAdd l n).succ

def toLevel : syntax → elaboratorM level
| stx := do
  (fn, args) ← levelGetAppArgs stx,
  sc ← currentScope,
  match fn.kind with
  | some level.leading := (match view level.leading fn, args with
    | level.leading.view.hole _, [] := pure $ level.mvar name.anonymous
    | level.leading.view.lit lit, [] := pure $ level.ofNat lit.toNat
    | level.leading.view.var id, [] := let id := mangleIdent id in (match sc.univs.find id with
      | some _ := pure $ level.param id
      | none   := error stx $ "unknown universe variable '" ++ toString id ++ "'")
    | level.leading.view.max _, (arg::args) := list.foldr level.max <$> toLevel arg <*> args.mmap toLevel
    | level.leading.view.imax _, (arg::args) := list.foldr level.imax <$> toLevel arg <*> args.mmap toLevel
    | _, _ := error stx "ill-formed universe level")
  | some level.trailing := (match view level.trailing fn, args with
    | level.trailing.view.addLit lta, [] := do
      l ← toLevel lta.lhs,
      pure $ levelAdd l lta.rhs.toNat
    | _, _ := error stx "ill-formed universe level")
  | _ := error stx $ "toLevel: unexpected input: " ++ toString stx

def expr.mkAnnotation (ann : name) (e : expr) :=
expr.mdata (kvmap.setName {} `annotation ann) e

def dummy : expr := expr.const `Prop []

def mkEqns (type : expr) (eqns : list (name × list expr × expr)): expr :=
  let eqns := eqns.map $ λ ⟨fn, lhs, rhs⟩, do {
    let fn := expr.local fn fn type binderInfo.auxDecl,
    let lhs := expr.mkApp (expr.mkAnnotation `@ fn) lhs,
    expr.app lhs rhs
  } in
  expr.mkAnnotation `preEquations $ expr.mkCapp `_ eqns

def toPexpr : syntax → elaboratorM expr
| stx@(syntax.rawNode {kind := k, args := args}) := do
  e ← match k with
  | @identUnivs := do
    let v := view identUnivs stx,
    e ← match v with
    | {id := id, univs := some univs} := expr.const (mangleIdent id) <$> univs.levels.mmap toLevel
    | {id := id, univs := none}       := pure $ expr.const (mangleIdent id) [],
    let m := kvmap.setName {} `annotation `preresolved,
    let m := v.id.preresolved.enum.foldl (λ m ⟨i, n⟩, kvmap.setName m (name.anonymous.mkNumeral i) n) m,
    pure $ expr.mdata m e
  | @app   := let v := view app stx in
    expr.app <$> toPexpr v.fn <*> toPexpr v.arg
  | @lambda := do
    let lam := view lambda stx,
    binders.view.simple bnder ← pure lam.binders
      | error stx "ill-formed lambda",
    (bi, id, type) ← pure bnder.toBinderInfo,
    expr.lam (mangleIdent id) bi <$> toPexpr type <*> toPexpr lam.body
  | @pi := do
    let v := view pi stx,
    binders.view.simple bnder ← pure v.binders
      | error stx "ill-formed pi",
    (bi, id, type) ← pure bnder.toBinderInfo,
    expr.pi (mangleIdent id) bi <$> toPexpr type <*> toPexpr v.range
  | @sort := (match view sort stx with
    | sort.view.Sort _ := pure $ expr.sort level.zero
    | sort.view.Type _ := pure $ expr.sort $ level.succ level.zero)
  | @sortApp := do
    let v := view sortApp stx,
    (match view sort v.fn with
     | sort.view.Sort _ := expr.sort <$> toLevel v.arg
     | sort.view.Type _ := (expr.sort ∘ level.succ) <$> toLevel v.arg)
  | @anonymousConstructor := do
    let v := view anonymousConstructor stx,
    p ← toPexpr $ mkApp (review hole {}) (v.args.map sepBy.elem.view.item),
    pure $ expr.mkAnnotation `anonymousConstructor p
  | @hole := pure $ expr.mvar name.anonymous dummy
  | @«have» := do
    let v := view «have» stx,
    let id := (mangleIdent <$> optIdent.view.id <$> v.id).getOrElse `this,
    let proof := match v.proof with
    | haveProof.view.term hpt := hpt.term
    | haveProof.view.from hpf := hpf.from.proof,
    lam ← expr.lam id binderInfo.default <$> toPexpr v.prop <*> toPexpr v.body,
    expr.app (expr.mkAnnotation `have lam) <$> toPexpr proof
  | @«show» := do
    let v := view «show» stx,
    prop ← toPexpr v.prop,
    proof ← toPexpr v.from.proof,
    pure $ expr.mkAnnotation `show $ expr.app (expr.lam `this binderInfo.default prop $ expr.bvar 0) proof
  | @«let» := do
    let v := view «let» stx,
    letLhs.view.id {id := id, binders := [], type := some ty} ← pure v.lhs
      | error stx "ill-formed let",
    expr.elet (mangleIdent id) <$> toPexpr ty.type <*> toPexpr v.value <*> toPexpr v.body
  | @projection := do
    let v := view projection stx,
    let val := match v.proj with
    | projectionSpec.view.id id := dataValue.ofName id.val
    | projectionSpec.view.num n := dataValue.ofNat n.toNat,
    expr.mdata (kvmap.insert {} `fieldNotation val) <$> toPexpr v.term
  | @explicit := do
    let v := view explicit stx,
    let ann := match v.mod with
    | explicitModifier.view.explicit _         := `@
    | explicitModifier.view.partialExplicit _ := `@@,
    expr.mkAnnotation ann <$> toPexpr (review identUnivs v.id)
  | @inaccessible := do
    let v := view inaccessible stx,
    expr.mkAnnotation `innaccessible <$> toPexpr v.term  -- sic
  | @borrowed := do
    let v := view borrowed stx,
    expr.mkAnnotation `borrowed <$> toPexpr v.term
  | @number := do
    let v := view number stx,
    pure $ expr.lit $ literal.natVal v.toNat
  | @stringLit := do
    let v := view stringLit stx,
    pure $ expr.lit $ literal.strVal (v.value.getOrElse "NOTAString")
  | @choice := do
    last::rev ← list.reverse <$> args.mmap (λ a, toPexpr a)
      | error stx "ill-formed choice",
    pure $ expr.mdata (kvmap.setNat {} `choice args.length) $
      rev.reverse.foldr expr.app last
  | @structInst := do
    let v := view structInst stx,
    -- order should be: fields*, sources*, catchall?
    let (fields, other) := v.items.span (λ it, ↑match sepBy.elem.view.item it with
      | structInstItem.view.field _ := tt
      | _ := ff),
    let (sources, catchall) := other.span (λ it, ↑match sepBy.elem.view.item it with
      | structInstItem.view.source {source := some _} := tt
      | _ := ff),
    catchall ← match catchall with
    | [] := pure ff
    | [{item := structInstItem.view.source _}] := pure tt
    | {item := it}::_ := error (review structInstItem it) $ "unexpected item in structure instance notation",

    fields ← fields.mmap (λ f, match sepBy.elem.view.item f with
      | structInstItem.view.field f :=
        expr.mdata (kvmap.setName {} `field $ mangleIdent f.id) <$> toPexpr f.val
      | _ := error stx "toPexpr: unreachable"),
    sources ← sources.mmap (λ src, match sepBy.elem.view.item src with
      | structInstItem.view.source {source := some src} := toPexpr src
      | _ := error stx "toPexpr: unreachable"),
    sources ← match v.with with
    | none     := pure sources
    | some src := do { src ← toPexpr src.source, pure $ sources ++ [src]},

    let m := kvmap.setNat {} "structure instance" fields.length,
    let m := kvmap.setBool m `catchall catchall,
    let m := kvmap.setName m `struct $
      (mangleIdent <$> structInstType.view.id <$> v.type).getOrElse name.anonymous,
    let dummy := expr.sort level.zero,
    pure $ expr.mdata m $ (fields ++ sources).foldr expr.app dummy
  | @«match» := do
    let v := view «match» stx,
    eqns ← (v.equations.map sepBy.elem.view.item).mmap $ λ (eqn : matchEquation.view), do {
      lhs ← eqn.lhs.mmap $ λ l, toPexpr l.item,
      rhs ← toPexpr eqn.rhs,
      pure (`_matchFn, lhs, rhs)
    },
    type ← toPexpr $ getOptType v.type,
    let eqns := mkEqns type eqns,
    expr.mdata mdata e ← pure eqns
      | error stx "toPexpr: unreachable",
    let eqns := expr.mdata (mdata.setBool `match tt) e,
    expr.mkApp eqns <$> v.scrutinees.mmap (λ scr, toPexpr scr.item)
  | _ := error stx $ "toPexpr: unexpected node: " ++ toString k.name,
  (match k with
  | @app := pure e -- no position
  | _ := do
    cfg ← read,
    match stx.getPos with
    | some pos :=
      let pos := cfg.fileMap.toPosition pos in
      pure $ expr.mdata ((kvmap.setNat {} `column pos.column).setNat `row pos.line) e
    | none := pure e)
| stx := error stx $ "toPexpr: unexpected: " ++ toString stx

/-- Returns the active namespace, that is, the concatenation of all active `namespace` commands. -/
def getNamespace : elaboratorM name := do
  sc ← currentScope,
  pure $ match sc.nsStack with
  | ns::_ := ns
  | _     := name.anonymous

def oldElabCommand (stx : syntax) (cmd : expr) : elaboratorM unit :=
do cfg ← read,
   let pos := cfg.fileMap.toPosition $ stx.getPos.getOrElse (default _),
   let cmd := match cmd with
   | expr.mdata m e := expr.mdata ((kvmap.setNat m `column pos.column).setNat `row pos.line) e
   | e := e,
   st ← get,
   sc ← currentScope,
   ns ← getNamespace,
   let (st', msgs) := elaborateCommand cfg.filename cmd {
     ns := ns,
     univs := sc.univs.entries.reverse,
     vars := sc.vars.entries.reverse,
     includeVars := sc.includeVars.toList,
     options := sc.options,
     ..st},
   match st' with
   | some st' := do modifyCurrentScope $ λ sc, {sc with
       univs := orderedRbmap.ofList st'.univs,
       vars := orderedRbmap.ofList st'.vars,
       includeVars := rbtree.ofList st'.includeVars,
       options := st'.options,
     },
     modify $ λ st, {..st', ..st}
   | none := pure (),  -- error
   modify $ λ st, {st with messages := st.messages ++ msgs}

def namesToPexpr (ns : list name) : expr :=
expr.mkCapp `_ $ ns.map (λ n, expr.const n [])

def attrsToPexpr (attrs : list (sepBy.elem.view attrInstance.view (option syntaxAtom))) : elaboratorM expr :=
expr.mkCapp `_ <$> attrs.mmap (λ attr,
  expr.mkCapp attr.item.name.val <$> attr.item.args.mmap toPexpr)

def declModifiersToPexpr (mods : declModifiers.view) : elaboratorM expr := do
  let mdata : kvmap := {},
  let mdata := match mods.docComment with
    | some {doc := some doc, ..} := mdata.setString `docString doc.val
    | _ := mdata,
  let mdata := match mods.visibility with
    | some (visibility.view.private _) := mdata.setBool `private tt
    | some (visibility.view.protected _) := mdata.setBool `protected tt
    | _ := mdata,
  let mdata := mdata.setBool `noncomputable mods.noncomputable.isSome,
  let mdata := mdata.setBool `unsafe mods.unsafe.isSome,
  expr.mdata mdata <$> attrsToPexpr (match mods.attrs with
    | some attrs := attrs.attrs
    | none       := [])

def identUnivParamsToPexpr (id : identUnivParams.view) : expr :=
expr.const (mangleIdent id.id) $ match id.univParams with
  | some params := params.params.map (level.param ∘ mangleIdent)
  | none        := []

/-- Execute `elab` and reset local scope (universes, ...) after it has finished. -/
def locally (elab : elaboratorM unit) :
  elaboratorM unit := do
  sc ← currentScope,
  elab,
  modifyCurrentScope $ λ _, sc

def simpleBindersToPexpr (bindrs : list simpleBinder.view) : elaboratorM expr :=
expr.mkCapp `_ <$> bindrs.mmap (λ b, do
  let (bi, id, type) := b.toBinderInfo,
  let id := mangleIdent id,
  type ← toPexpr type,
  pure $ expr.local id id type bi)

def elabDefLike (stx : syntax) (mods : declModifiers.view) (dl : defLike.view) (kind : nat) : elaboratorM unit :=
match dl with
| {sig := {params := bracketedBinders.view.simple bbs}, ..} := do
  let mdata := kvmap.setName {} `command `defs,
  mods ← declModifiersToPexpr mods,
  let kind := expr.lit $ literal.natVal kind,
  match dl.oldUnivParams with
  | some uparams :=
    modifyCurrentScope $ λ sc, {sc with univs :=
      (uparams.ids.map mangleIdent).foldl (λ m id, orderedRbmap.insert m id (level.param id)) sc.univs}
  | none := pure (),
  -- do we actually need this??
  let uparams := namesToPexpr $ match dl.oldUnivParams with
  | some uparams := uparams.ids.map mangleIdent
  | none := [],
  let id := mangleIdent dl.name.id,
  let type := getOptType dl.sig.type,
  type ← toPexpr type,
  let fns := expr.mkCapp `_ [expr.local id id type binderInfo.auxDecl],
  val ← match dl.val with
  | declVal.view.simple val  := toPexpr val.body
  | declVal.view.emptyMatch _ := pure $ mkEqns type []
  | declVal.view.match eqns  := do {
    eqns ← eqns.mmap (λ (eqn : equation.view), do
      lhs ← eqn.lhs.mmap toPexpr,
      rhs ← toPexpr eqn.rhs,
      pure (id, lhs, rhs)
    ),
    pure $ mkEqns type eqns
  },
  params ← simpleBindersToPexpr bbs,
  oldElabCommand stx $ expr.mdata mdata $ expr.mkCapp `_ [mods, kind, uparams, fns, params, val]
| _ := error stx "elabDefLike: unexpected input"

def inferModToPexpr (mod : option inferModifier.view) : expr :=
expr.lit $ literal.natVal $ match mod with
| none := 0
| some $ inferModifier.view.relaxed _ := 1
| some $ inferModifier.view.strict _  := 2

def declaration.elaborate : elaborator :=
λ stx, locally $ do
  let decl := view «declaration» stx,
  match decl.inner with
  | declaration.inner.view.«axiom» c@{sig := {params := bracketedBinders.view.simple [], type := type}, ..} := do
    let mdata := kvmap.setName {} `command `«axiom», -- CommentTo(Kha): It was `constant` here
    mods ← declModifiersToPexpr decl.modifiers,
    let id := identUnivParamsToPexpr c.name,
    type ← toPexpr type.type,
    oldElabCommand stx $ expr.mdata mdata $ expr.mkCapp `_ [mods, id, type]
  | declaration.inner.view.defLike dl := do
      -- The numeric literals below should reflect the enum values
      -- enum class declCmdKind { Theorem, Definition, OpaqueConst, Example, Instance, Var, Abbreviation };
      let kind := match dl.kind with
      | defLike.kind.view.theorem _ := 0
      | defLike.kind.view.def _ := 1
      | defLike.kind.view.«constant» _ := 2
      | defLike.kind.view.abbreviation _ := 6
      | defLike.kind.view.«abbrev» _ := 6,
      elabDefLike stx decl.modifiers dl kind

  -- these are almost macros for `def`, except the elaborator handles them specially at a few places
  -- based on the kind
  | declaration.inner.view.example ex :=
    elabDefLike stx decl.modifiers {
      kind := defLike.kind.view.def,
      name := {id := name.anonymous},
      sig := {..ex.sig},
      ..ex} 3
  | declaration.inner.view.instance i :=
    elabDefLike stx decl.modifiers {
      kind := defLike.kind.view.def,
      name := i.name.getOrElse {id := name.anonymous},
      sig := {..i.sig},
      ..i} 4

  | declaration.inner.view.inductive ind@{«class» := none, sig := {params := bracketedBinders.view.simple bbs}, ..} := do
    let mdata := kvmap.setName {} `command `inductives,
    mods ← declModifiersToPexpr decl.modifiers,
    attrs ← attrsToPexpr (match decl.modifiers.attrs with
      | some attrs := attrs.attrs
      | none       := []),
    let mutAttrs := expr.mkCapp `_ [attrs],
    match ind.oldUnivParams with
    | some uparams :=
      modifyCurrentScope $ λ sc, {sc with univs :=
        (uparams.ids.map mangleIdent).foldl (λ m id, orderedRbmap.insert m id (level.param id)) sc.univs}
    | none := pure (),
    let uparams := namesToPexpr $ match ind.oldUnivParams with
    | some uparams := uparams.ids.map mangleIdent
    | none := [],
    let id := mangleIdent ind.name.id,
    let type := getOptType ind.sig.type,
    type ← toPexpr type,
    let indL := expr.local id id type binderInfo.default,
    let inds := expr.mkCapp `_ [indL],
    params ← simpleBindersToPexpr bbs,
    introRules ← ind.introRules.mmap (λ (r : introRule.view), do
      ({params := bracketedBinders.view.simple [], type := some ty}) ← pure r.sig
        | error stx "declaration.elaborate: unexpected input",
      type ← toPexpr ty.type,
      let name := mangleIdent r.name,
      pure $ expr.local name name type binderInfo.default),
    let introRules := expr.mkCapp `_ introRules,
    let introRules := expr.mkCapp `_ [introRules],
    let inferKinds := ind.introRules.map $ λ (r : introRule.view), inferModToPexpr r.inferMod,
    let inferKinds := expr.mkCapp `_ inferKinds,
    let inferKinds := expr.mkCapp `_ [inferKinds],
    oldElabCommand stx $ expr.mdata mdata $
      expr.mkCapp `_ [mods, mutAttrs, uparams, inds, params, introRules, inferKinds]

  | declaration.inner.view.structure s@{keyword := structureKw.view.structure _, sig := {params := bracketedBinders.view.simple bbs}, ..} := do
    let mdata := kvmap.setName {} `command `structure,
    mods ← declModifiersToPexpr decl.modifiers,
    match s.oldUnivParams with
    | some uparams :=
      modifyCurrentScope $ λ sc, {sc with univs :=
        (uparams.ids.map mangleIdent).foldl (λ m id, orderedRbmap.insert m id (level.param id)) sc.univs}
    | none := pure (),
    let uparams := namesToPexpr $ match s.oldUnivParams with
    | some uparams := uparams.ids.map mangleIdent
    | none := [],
    let name := mangleIdent s.name.id,
    let name := expr.local name name dummy binderInfo.default,
    let type := getOptType s.sig.type,
    type ← toPexpr type,
    params ← simpleBindersToPexpr bbs,
    let parents := match s.extends with
    | some ex := ex.parents
    | none    := [],
    parents ← parents.mmap (toPexpr ∘ sepBy.elem.view.item),
    let parents := expr.mkCapp `_ parents,
    let mk := match s.ctor with
    | some ctor := mangleIdent ctor.name
    | none      := `mk,
    let mk := expr.local mk mk dummy binderInfo.default,
    let infer := inferModToPexpr (s.ctor >>= structureCtor.view.inferMod),
    fieldBlocks ← s.fieldBlocks.mmap (λ bl, do
      (bi, content) ← match bl with
        | structureFieldBlock.view.explicit {content := structExplicitBinderContent.view.notation _} :=
          error stx "declaration.elaborate: unexpected input"
        | structureFieldBlock.view.explicit {content := structExplicitBinderContent.view.other c} :=
          pure (binderInfo.default, c)
        | structureFieldBlock.view.implicit {content := c} := pure (binderInfo.implicit, c)
        | structureFieldBlock.view.strictImplicit {content := c} := pure (binderInfo.strictImplicit, c)
        | structureFieldBlock.view.instImplicit {content := c} := pure (binderInfo.instImplicit, c),
      let bi := expr.local `_ `_ dummy bi,
      let ids := namesToPexpr $ content.ids.map mangleIdent,
      let kind := inferModToPexpr content.inferMod,
      let type := getOptType content.sig.type,
      type ← toPexpr type,
      pure $ expr.mkCapp `_ [bi, ids, kind, type]),
    let fieldBlocks := expr.mkCapp `_ fieldBlocks,
    oldElabCommand stx $ expr.mdata mdata $
      expr.mkCapp `_ [mods, uparams, name, params, parents, type, mk, infer, fieldBlocks]
  | _ :=
    error stx "declaration.elaborate: unexpected input"

def variables.elaborate : elaborator :=
λ stx, do
  let mdata := kvmap.setName {} `command `variables,
  let v := view «variables» stx,
  vars ← match v.binders with
  | bracketedBinders.view.simple bbs := bbs.mfilter $ λ b, do
    let (bi, id, type) := b.toBinderInfo,
    if type.isOfKind bindingAnnotationUpdate then do
      sc ← currentScope,
      let id := mangleIdent id,
      match sc.vars.find id with
      | some (_, v) :=
        modifyCurrentScope $ λ sc, {sc with vars :=
          sc.vars.insert id {v with binderInfo := bi}}
      | none := error (syntax.ident id) "",
      pure ff
    else pure tt
  | _ := error stx "variables.elaborate: unexpected input",
  vars ← simpleBindersToPexpr vars,
  oldElabCommand stx $ expr.mdata mdata vars

def include.elaborate : elaborator :=
λ stx, do
  let v := view «include» stx,
  -- TODO(Sebastian): error checking
  modifyCurrentScope $ λ sc, {sc with includeVars :=
    v.ids.foldl (λ vars v, vars.insert $ mangleIdent v) sc.includeVars}

-- TODO: rbmap.remove
/-
def omit.elaborate : elaborator :=
λ stx, do
  let v := view «omit» stx,
  modify $ λ st, {st with localState := {sc with includeVars :=
    v.ids.foldl (λ vars v, vars.remove $ mangleIdent v) sc.includeVars}}
-/

def module.header.elaborate : elaborator :=
λ stx, do
  let header := view module.header stx,
  match header with
  | {«prelude» := some _, imports := []} := pure ()
  | _ := error stx "not implemented: imports"

def precToNat : option precedence.view → nat
| (some prec) := prec.term.toNat
| none        := 0

-- TODO(Sebastian): Command parsers like `structure` will need access to these
def commandParserConfig.registerNotationTokens (spec : notationSpec.view) (cfg : commandParserConfig) :
  except string commandParserConfig :=
do spec.rules.mfoldl (λ (cfg : commandParserConfig) r, match r.symbol with
   | notationSymbol.view.quoted {symbol := some a, prec := prec, ..} :=
     pure {cfg with tokens := cfg.tokens.insert a.val.trim {«prefix» := a.val.trim, lbp := precToNat prec}}
   | _ := throw "registerNotationTokens: unreachable") cfg

def commandParserConfig.registerNotationParser (k : syntaxNodeKind) (nota : notation.view)
  (cfg : commandParserConfig) : except string commandParserConfig :=
do -- build and register parser
   ps ← nota.spec.rules.mmap (λ r : rule.view, do
     psym ← match r.symbol with
     | notationSymbol.view.quoted {symbol := some a ..} :=
       pure (symbol a.val : termParser)
     | _ := throw "registerNotationParser: unreachable",
     ptrans ← match r.transition with
     | some (transition.view.binder b) :=
       pure $ some $ term.binderIdent.parser
     | some (transition.view.binders b) :=
       pure $ some $ term.binders.parser
     | some (transition.view.arg {action := none, ..}) :=
       pure $ some term.parser
     | some (transition.view.arg {action := some {kind := actionKind.view.prec prec}, ..}) :=
       pure $ some $ term.parser prec.toNat
     | some (transition.view.arg {action := some {kind := actionKind.view.scoped sc}, ..}) :=
       pure $ some $ term.parser $ precToNat sc.prec
     | none := pure $ none
     | _ := throw "registerNotationParser: unimplemented",
     pure $ psym::ptrans.toMonad
   ),
   firstRule::_ ← pure nota.spec.rules | throw "registerNotationParser: unreachable",
   firstTk ← match firstRule.symbol with
   | notationSymbol.view.quoted {symbol := some a ..} :=
     pure a.val.trim
   | _ := throw "registerNotationParser: unreachable",
   let ps := ps.bind id,
   cfg ← match nota.local, nota.spec.prefixArg with
   | none,   none   := pure {cfg with leadingTermParsers :=
     cfg.leadingTermParsers.insert firstTk $ parser.combinators.node k ps}
   | some _, none   := pure {cfg with localLeadingTermParsers :=
     cfg.localLeadingTermParsers.insert firstTk $ parser.combinators.node k ps}
   | none,   some _ := pure {cfg with trailingTermParsers :=
     cfg.trailingTermParsers.insert firstTk $ parser.combinators.node k (getLeading::ps.map coe)}
   | some _, some _ := pure {cfg with localTrailingTermParsers :=
     cfg.localTrailingTermParsers.insert firstTk $ parser.combinators.node k (getLeading::ps.map coe)},
   pure cfg

/-- Recreate `elaboratorState.parserCfg` from the elaborator state and the initial config,
    effectively treating it as a cache. -/
def updateParserConfig : elaboratorM unit :=
do st ← get,
   sc ← currentScope,
   cfg ← read,
   let ccfg := cfg.initialParserCfg.toCommandParserConfig,
   ccfg ← st.reservedNotations.mfoldl (λ ccfg rnota,
     match commandParserConfig.registerNotationTokens rnota.spec ccfg with
     | except.ok ccfg := pure ccfg
     | except.error e := error (review reserveNotation rnota) e) ccfg,
   ccfg ← (st.notations ++ sc.notations).mfoldl (λ ccfg nota,
     match commandParserConfig.registerNotationTokens nota.nota.spec ccfg >>=
               commandParserConfig.registerNotationParser nota.kind nota.nota with
     | except.ok ccfg := pure ccfg
     | except.error e := error (review «notation» nota.nota) e) ccfg,
   put {st with parserCfg := {cfg.initialParserCfg with toCommandParserConfig := ccfg}}

def postprocessNotationSpec (spec : notationSpec.view) : notationSpec.view :=
-- default leading tokens to `max`
-- NOTE: should happen after copying precedences from reserved notation
match spec with
| {prefixArg := none, rules := r@{symbol := notationSymbol.view.quoted sym@{prec := none, ..}, ..}::rs} :=
  {spec with rules := {r with symbol := notationSymbol.view.quoted {sym with prec := some
    {term := precedenceTerm.view.lit $ precedenceLit.view.num $ number.view.ofNat maxPrec}
  }}::rs}
| _ := spec

def reserveNotation.elaborate : elaborator :=
λ stx, do
  let v := view reserveNotation stx,
  let v := {v with spec := postprocessNotationSpec v.spec},
  -- TODO: sanity checks?
  modify $ λ st, {st with reservedNotations := v::st.reservedNotations},
  updateParserConfig

def matchPrecedence : option precedence.view → option precedence.view → bool
| none      (some rp) := tt
| (some sp) (some rp) := sp.term.toNat = rp.term.toNat
| _         _         := ff

/-- Check if a notation is compatible with a reserved notation, and if so, copy missing
    precedences in the notation from the reserved notation. -/
def matchSpec (spec reserved : notationSpec.view) : option notationSpec.view :=
do guard $ spec.prefixArg.isSome = reserved.prefixArg.isSome,
   rules ← (spec.rules.zip reserved.rules).mmap $ λ ⟨sr, rr⟩, do {
     notationSymbol.view.quoted sq@{symbol := some sa, ..} ← pure sr.symbol
       | failure,
     notationSymbol.view.quoted rq@{symbol := some ra, ..} ← pure rr.symbol
       | failure,
     guard $ sa.val.trim = ra.val.trim,
     guard $ matchPrecedence sq.prec rq.prec,
     st ← match sr.transition, rr.transition with
     | some (transition.view.binder sb), some (transition.view.binder rb) :=
       guard (matchPrecedence sb.prec rb.prec) *> pure rr.transition
     | some (transition.view.binders sb), some (transition.view.binders rb) :=
       guard (matchPrecedence sb.prec rb.prec) *> pure rr.transition
     | some (transition.view.arg sarg), some (transition.view.arg rarg) := do
       sact ← match action.view.kind <$> sarg.action, action.view.kind <$> rarg.action with
       | some (actionKind.view.prec sp), some (actionKind.view.prec rp) :=
         guard (sp.toNat = rp.toNat) *> pure sarg.action
       | none,                            some (actionKind.view.prec rp) :=
         pure rarg.action
       | _, _ := failure,
       pure $ some $ transition.view.arg {sarg with action := sact}
     | none,    none    := pure none
     | _,       _       := failure,
     pure $ {rule.view .
       symbol := notationSymbol.view.quoted rq,
       transition := st}
   },
   pure $ {spec with rules := rules}

def notation.elaborateAux : notation.view → elaboratorM notation.view :=
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

-- TODO(Sebastian): better kind names, module prefix?
def mkNotationKind : elaboratorM syntaxNodeKind :=
do st ← get,
   put {st with notationCounter := st.notationCounter + 1},
   pure {name := (`_notation).mkNumeral st.notationCounter}

/-- Register a notation in the expander. Unlike with notation parsers, there is no harm in
    keeping local notation macros registered after closing a section. -/
def registerNotationMacro (nota : notation.view) : elaboratorM notationMacro :=
do k ← mkNotationKind,
   let m : notationMacro := ⟨k, nota⟩,
   let transf := mkNotationTransformer m,
   modify $ λ st, {st with expanderCfg := {st.expanderCfg with transformers := st.expanderCfg.transformers.insert k.name transf}},
   pure m

def notation.elaborate : elaborator :=
λ stx, do
  let nota := view «notation» stx,
  -- HACK: ignore list literal notation using :fold
  let usesFold := nota.spec.rules.any $ λ r, match r.transition with
    | some (transition.view.arg {action := some {kind := actionKind.view.fold _, ..}, ..}) := tt
    | _ := ff,
  if usesFold then do {
    cfg ← read,
    modify $ λ st, {st with messages := st.messages.add {filename := cfg.filename, pos := ⟨1,0⟩,
      severity := messageSeverity.warning, text := "ignoring notation using 'fold' action"}}
  } else do {
    nota ← notation.elaborateAux nota,
    m ← registerNotationMacro nota,
    match nota.local with
      | some _ := modifyCurrentScope $ λ sc, {sc with notations := m::sc.notations}
      | none   := modify $ λ st, {st with notations := m::st.notations},
    updateParserConfig
  }

def universe.elaborate : elaborator :=
λ stx, do
  let univ := view «universe» stx,
  let id := mangleIdent univ.id,
  sc ← currentScope,
  match sc.univs.find id with
  | none   := modifyCurrentScope $ λ sc, {sc with univs := sc.univs.insert id (level.param id)}
  | some _ := error stx $ "a universe named '" ++ toString id ++ "' has already been declared in this scope"

def attribute.elaborate : elaborator :=
λ stx, do
  let attr := view «attribute» stx,
  let mdata := kvmap.setName {} `command `attribute,
  let mdata := mdata.setBool `local $ attr.local.isSome,
  attrs ← attrsToPexpr attr.attrs,
  ids ← attr.ids.mmap (λ id, match id.preresolved with
    | []  := error (syntax.ident id) $ "unknown identifier '" ++ toString id.val ++ "'"
    | [c] := pure $ expr.const c []
    | _   := error (syntax.ident id) "invalid 'attribute' command, identifier is ambiguous"),
  let ids := expr.mkCapp `_ ids,
  oldElabCommand stx $ expr.mdata mdata $ expr.app attrs ids

def check.elaborate : elaborator :=
λ stx, do
  let v := view check stx,
  let mdata := kvmap.setName {} `command `#check,
  e ← toPexpr v.term,
  oldElabCommand stx $ expr.mdata mdata e

def open.elaborate : elaborator :=
λ stx, do
  let v := view «open» stx,
  -- TODO: do eager sanity checks (namespace does not exist, etc.)
  modifyCurrentScope $ λ sc, {sc with openDecls := sc.openDecls ++ v.spec}

def export.elaborate : elaborator :=
λ stx, do
  let v := view «export» stx,
  ns ← getNamespace,
  -- TODO: do eager sanity checks (namespace does not exist, etc.)
  modify $ λ st, {st with exportDecls := st.exportDecls ++ v.spec.map (λ spec, ⟨ns, spec⟩)}

def initQuot.elaborate : elaborator :=
λ stx, oldElabCommand stx $ expr.mdata (kvmap.setName {} `command `initQuot) dummy

def setOption.elaborate : elaborator :=
λ stx, do
  let v := view «setOption» stx,
  let opt := v.opt.val,
  sc ← currentScope,
  let opts := sc.options,
  -- TODO(Sebastian): check registered options
  let opts := match v.val with
  | optionValue.view.bool b := opts.setBool opt (match b with boolOptionValue.view.true _ := tt | _ := ff)
  | optionValue.view.string lit := (match lit.value with
    | some s := opts.setString opt s
    | none   := opts)  -- parser already failed
  | optionValue.view.num lit := opts.setNat opt lit.toNat,
  modifyCurrentScope $ λ sc, {sc with options := opts}

/-- List of commands: recursively elaborate each command. -/
def noKind.elaborate : elaborator := λ stx, do
  some n ← pure stx.asNode
    | error stx "noKind.elaborate: unreachable",
  n.args.mmap' command.elaborate

def end.elaborate : elaborator :=
λ cmd, do
  let v := view «end» cmd,
  st ← get,
  -- NOTE: bottom-most (module) scope cannot be closed
  sc::sc'::scps ← pure st.scopes
    | error cmd "invalid 'end', there is no open scope to end",
  let endName := mangleIdent $ v.name.getOrElse name.anonymous,
  when (endName ≠ sc.header) $
    error cmd $ "invalid end of " ++ sc.cmd ++ ", expected name '" ++
      toString sc.header ++ "'",
  put {st with scopes := sc'::scps},
  -- local notations may have vanished
  updateParserConfig

def section.elaborate : elaborator :=
λ cmd, do
  let sec := view «section» cmd,
  let header := mangleIdent $ sec.name.getOrElse name.anonymous,
  sc ← currentScope,
  modify $ λ st, {st with scopes := {sc with cmd := "section", header := header}::st.scopes}

def namespace.elaborate : elaborator :=
λ cmd, do
  let v := view «namespace» cmd,
  let header := mangleIdent v.name,
  sc ← currentScope,
  ns ← getNamespace,
  let sc' := {sc with cmd := "namespace", header := header, nsStack := (ns ++ header)::sc.nsStack},
  modify $ λ st, {st with scopes := sc'::st.scopes}

def eoi.elaborate : elaborator :=
λ cmd, do
  st ← get,
  when (st.scopes.length > 1) $
    error cmd "invalid end of input, expected 'end'"

-- TODO(Sebastian): replace with attribute
def elaborators : rbmap name elaborator (<) := rbmap.fromList [
  (module.header.name, module.header.elaborate),
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
  (module.eoi.name, eoi.elaborate)
] _

-- TODO: optimize
def isOpenNamespace (sc : scope) : name → bool
| name.anonymous := tt
| ns :=
  -- check surrounding namespaces
  ns ∈ sc.nsStack ∨
  -- check opened namespaces
  sc.openDecls.any (λ od, od.id.val = ns) ∨
  -- TODO: check active exports
  ff

-- TODO: `hiding`, `as`, `renaming`
def matchOpenSpec (n : name) (spec : openSpec.view) : option name :=
let matchesOnly := match spec.only with
| none := tt
| some only := n = only.id.val ∨ only.ids.any (λ id, n = id.val) in
if matchesOnly then some (spec.id.val ++ n) else none

def resolveContext : name → elaboratorM (list name)
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
  (let unrooted := n.replacePrefix `_root_ name.anonymous in
   match st.env.contains unrooted with
   | tt := [unrooted]
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

def preresolve : syntax → elaboratorM syntax
| (syntax.ident id) := do
  let n := mangleIdent id,
  ns ← resolveContext n,
  pure $ syntax.ident {id with preresolved := ns ++ id.preresolved}
| (syntax.rawNode n) := do
  args ← n.args.mmap preresolve,
  pure $ syntax.rawNode {n with args := args}
| stx := pure stx

def mkState (cfg : elaboratorConfig) (env : environment) (opts : options) : elaboratorState := {
  parserCfg := cfg.initialParserCfg,
  expanderCfg := {transformers := expander.builtinTransformers, ..cfg},
  env := env,
  ngen := ⟨`_ngen.fixme, 0⟩,
  scopes := [{cmd := "MODULE", header := `MODULE, options := opts}]}

def processCommand (cfg : elaboratorConfig) (st : elaboratorState) (cmd : syntax) : elaboratorState :=
let st := {st with messages := messageLog.empty} in
let r := @exceptT.run _ id _ $ flip stateT.run st $ flip readerT.run cfg $ recT.run
  (command.elaborate cmd)
  (λ _, error cmd "elaborator.run: recursion depth exceeded")
  (λ cmd, do
    some n ← pure cmd.asNode |
      error cmd $ "not a command: " ++ toString cmd,
    some elab ← pure $ elaborators.find n.kind.name |
      error cmd $ "unknown command: " ++ toString n.kind.name,
    cmd' ← preresolve cmd,
    elab cmd') in
match r with
| except.ok ((), st) := st
| except.error e     := {st with messages := st.messages.add e}

end elaborator
end lean
