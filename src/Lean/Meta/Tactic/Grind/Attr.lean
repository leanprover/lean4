/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Injective
public import Lean.Meta.Tactic.Grind.Cases
public import Lean.Meta.Tactic.Grind.ExtAttr
public import Lean.Meta.Tactic.Simp.Attr
public import Lean.Meta.Tactic.Grind.Homo
public import Lean.Meta.Sym.DSimp.Rewrite
import Lean.Meta.Sym.Simp.Attr
import Lean.ExtraModUses
public section
namespace Lean.Meta.Grind

builtin_initialize normExt : SimpExtension ← mkSimpExt

builtin_initialize registerTraceClass `grind.norm.sym

/--
The `grind` normalization theorems as `Sym.simp` theorem sets, the state of `normSymExt`. The
`[grind norm]`/`[grind unfold]` attributes populate it together with `normExt`, so both
normalizers see the same declarations.
-/
structure NormSymTheorems where
  /-- Theorems applied before visiting subterms (`[grind norm ↓]`). -/
  pre  : Sym.Simp.Theorems := {}
  /-- Theorems applied after visiting subterms (`[grind norm]`), and the equational theorems
  of the declarations to unfold (`[grind unfold]`). -/
  post : Sym.Simp.Theorems := {}
  /-- The `rfl`-theorems of `post` and the declarations to unfold, for `Sym.dsimp`. `grind` needs
  `dsimp` in one place: the right-hand side of a generalized pattern (`mkGeneralizedPatternEqProof`)
  must stay definitionally equal to the term it replaces, e.g. `Nat.succ x` becomes `x + 1`. -/
  dsimp : Sym.DSimp.Decls := {}
  deriving Inhabited

/-- An entry of `normSymExt`. -/
inductive NormSymEntry where
  | pre (thm : Sym.Simp.Theorem)
  | post (thm : Sym.Simp.Theorem)
  | dsimp (entry : Sym.DSimp.Decls.Entry)
  deriving Inhabited

def NormSymTheorems.addEntry (s : NormSymTheorems) : NormSymEntry → NormSymTheorems
  | .pre thm => { s with pre := s.pre.insert thm }
  | .post thm => { s with post := s.post.insert thm }
  | .dsimp e => { s with dsimp := s.dsimp.addEntry e }

/-- The declaration an entry refers to; entries on private declarations are not exported. -/
private def NormSymEntry.declName? : NormSymEntry → Option Name
  | .pre thm | .post thm | .dsimp (.thm thm) => match thm.expr with
    | .const declName _ => some declName
    | _ => none
  | .dsimp (.unfold declName) => some declName

builtin_initialize normSymExt : SimpleScopedEnvExtension NormSymEntry NormSymTheorems ←
  registerSimpleScopedEnvExtension {
    initial  := {}
    addEntry := NormSymTheorems.addEntry
    exportEntry? := fun _ e =>
      if let some declName := e.declName? then
        if isPrivateName declName then ⟨none, none, some e⟩ else .uniform (some e)
      else .uniform (some e)
  }

/-- The `Sym.simp` theorem of a `[grind norm]` theorem, or `none` if it cannot be converted. -/
private def mkNormSymTheorem? (thm : SimpTheorem) : MetaM (Option Sym.Simp.Theorem) := do
  -- Global simp theorems, including the reversed ones (`[grind norm ←]`), are stored as
  -- constants: `mkSimpTheoremFromConst` creates an auxiliary lemma when it has to adapt the
  -- statement.
  let .const declName _ := thm.proof
    | trace[grind.norm.sym] "skipping `{thm.origin.key}`, not a global declaration"
      return none
  try
    return some (← Sym.Simp.mkTheoremFromDecl declName)
  catch ex =>
    trace[grind.norm.sym] "skipping `{.ofConstName declName}`: {ex.toMessageData}"
    return none

/-- Adds the `[grind norm]` theorem `declName` to `normExt` and `normSymExt`. -/
def addNormTheorem (declName : Name) (post inv : Bool) (attrKind : AttributeKind) (prio : Nat := eval_prio default) : MetaM Unit := do
  let simpThms ← withExporting (isExporting := attrKind != .local && !isPrivateName declName) do
    mkSimpTheoremFromConst declName post inv prio (checkLhs := true)
  for simpThm in simpThms do
    normExt.add (.thm simpThm) attrKind
    let some thm ← mkNormSymTheorem? simpThm | continue
    normSymExt.add (if post then .post thm else .pre thm) attrKind
    if post && simpThm.rfl then
      normSymExt.add (.dsimp (.thm thm)) attrKind

/-- Adds the `[grind unfold]` declaration `declName` to `normSymExt`. -/
def addNormSymDeclToUnfold (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  -- `Sym` preprocessing unfolds reducible declarations (e.g., `GE.ge`, `Ne`) eagerly.
  if (← isReducible declName) then return
  try
    for thm in (← Sym.Simp.mkTheoremsFromDecl declName) do
      normSymExt.add (.post thm) attrKind
    for e in (← Sym.DSimp.Decls.mkEntries declName) do
      normSymExt.add (.dsimp e) attrKind
  catch ex =>
    trace[grind.norm.sym] "skipping unfold `{.ofConstName declName}`: {ex.toMessageData}"

/--
Adds the `[grind unfold]` declaration `declName` to `normExt` and `normSymExt`. Returns `false`
if the declaration cannot be unfolded.
-/
def addNormDeclToUnfold (declName : Name) (attrKind : AttributeKind) : MetaM Bool := do
  unless (← addDeclToUnfold normExt declName (post := false) (inv := false) (prio := eval_prio default) (attrKind := attrKind)) do
    return false
  addNormSymDeclToUnfold declName attrKind
  return true

inductive AttrKind where
  | ematch (k : EMatchTheoremKind)
  | cases (eager : Bool)
  | intro
  | infer
  | ext
  | symbol (prio : Nat)
  | inj
  | funCC
  | norm (post : Bool) (inv : Bool)
  | unfold
  | homo (fallback : Bool)
  | homoPred

/-- Return theorem kind for `stx` of the form `Attr.grindThmMod` -/
def getAttrKindCore (stx : Syntax) : CoreM AttrKind := do
  match stx with
  | `(Parser.Attr.grindMod|=) => return .ematch (.eqLhs false)
  | `(Parser.Attr.grindMod|.) => return .ematch (.default false)
  | `(Parser.Attr.grindMod|= gen) => return .ematch (.eqLhs true)
  | `(Parser.Attr.grindMod|→) => return .ematch .fwd
  | `(Parser.Attr.grindMod|←) => return .ematch (.bwd false)
  | `(Parser.Attr.grindMod|. gen) => return .ematch (.default true)
  | `(Parser.Attr.grindMod|← gen) => return .ematch (.bwd true)
  | `(Parser.Attr.grindMod|=_) => return .ematch (.eqRhs false)
  | `(Parser.Attr.grindMod|=_ gen) => return .ematch (.eqRhs true)
  | `(Parser.Attr.grindMod|_=_) => return .ematch (.eqBoth false)
  | `(Parser.Attr.grindMod|_=_ gen) => return .ematch (.eqBoth true)
  | `(Parser.Attr.grindMod|←=) => return .ematch .eqBwd
  | `(Parser.Attr.grindMod|=>) => return .ematch .leftRight
  | `(Parser.Attr.grindMod|<=) => return .ematch .rightLeft
  | `(Parser.Attr.grindMod|usr) => return .ematch .user
  | `(Parser.Attr.grindMod|gen) => return .ematch (.default true)
  | `(Parser.Attr.grindMod|cases) => return .cases false
  | `(Parser.Attr.grindMod|cases eager) => return .cases true
  | `(Parser.Attr.grindMod|intro) => return .intro
  | `(Parser.Attr.grindMod|ext) => return .ext
  | `(Parser.Attr.grindMod|inj) => return .inj
  | `(Parser.Attr.grindMod|funCC) => return .funCC
  | `(Parser.Attr.grindMod|norm) => return .norm true false
  | `(Parser.Attr.grindMod|norm ↑) => return .norm true false
  | `(Parser.Attr.grindMod|norm ↓) => return .norm (post := false) false
  | `(Parser.Attr.grindMod|norm ←) => return .norm true true
  | `(Parser.Attr.grindMod|norm ↑ ←) => return .norm true true
  | `(Parser.Attr.grindMod|norm ↓ ←) => return .norm (post := false) true
  | `(Parser.Attr.grindMod|unfold) => return .unfold
  | `(Parser.Attr.grindMod|hom) => return .homo (fallback := false)
  | `(Parser.Attr.grindMod|hom fallback) => return .homo (fallback := true)
  | `(Parser.Attr.grindMod|hom_pred) => return .homoPred
  | `(Parser.Attr.grindMod|symbol $prio:prio) =>
    let some prio := prio.raw.isNatLit? | throwErrorAt prio "priority expected"
    return .symbol prio
  | _ => throwError "unexpected `grind` theorem kind: `{stx}`"

/-- Return theorem kind for `stx` of the form `(Attr.grindMod)?` -/
def getAttrKindFromOpt (stx : Syntax) : CoreM AttrKind := do
  if stx[1].isNone then
    return .infer
  else
    getAttrKindCore stx[1][0]

def throwInvalidUsrModifier : CoreM α :=
  throwError "the modifier `usr` is only relevant in parameters for `grind only`"

private def Extension.addCasesAttr (ext : Extension) (declName : Name) (eager : Bool) (attrKind : AttributeKind) : CoreM Unit := do
  validateCasesAttr declName eager
  ext.add (.cases declName eager) attrKind

private def Extension.addExtAttr (ext : Extension) (declName : Name) (attrKind : AttributeKind) : CoreM Unit := do
  validateExtAttr declName
  ext.add (.ext declName) attrKind

private def Extension.addFunCCAttr (ext : Extension) (declName : Name) (attrKind : AttributeKind) : CoreM Unit := do
  ext.add (.funCC declName) attrKind

private def Extension.eraseExtAttr (ext : Extension) (declName : Name) : CoreM Unit := do
  let s := ext.getState (← getEnv)
  let extThms ← s.extThms.eraseDecl declName
  modifyEnv fun env => ext.modifyState env fun s => { s with extThms }

private def Extension.eraseCasesAttr (ext : Extension) (declName : Name) : CoreM Unit := do
  ensureNotBuiltinCases declName
  let s := ext.getState (← getEnv)
  let casesTypes ← s.casesTypes.eraseDecl declName
  modifyEnv fun env => ext.modifyState env fun s => { s with casesTypes }

private def Extension.eraseFunCCAttr (ext : Extension) (declName : Name) : CoreM Unit := do
  let s := ext.getState (← getEnv)
  unless s.funCC.contains declName do
    throwNotMarkedWithGrindAttribute declName
  let funCC := s.funCC.erase declName
  modifyEnv fun env => ext.modifyState env fun s => { s with funCC }

private def Extension.eraseEMatchAttr (ext : Extension) (declName : Name) : MetaM Unit := do
  let s := ext.getState (← getEnv)
  let ematch ← s.ematch.eraseDecl declName
  modifyEnv fun env => ext.modifyState env fun s => { s with ematch }

private def Extension.eraseInjectiveAttr (ext : Extension) (declName : Name) : MetaM Unit := do
  let s := ext.getState (← getEnv)
  let inj ← s.inj.eraseDecl declName
  modifyEnv fun env => ext.modifyState env fun s => { s with inj }

private def Extension.isExtTheorem (ext : Extension) (declName : Name) : CoreM Bool := do
  return ext.getState (← getEnv) |>.extThms.contains declName

private def Extension.isInjectiveTheorem (ext : Extension) (declName : Name) : CoreM Bool := do
  return ext.getState (← getEnv) |>.inj.contains (.decl declName)

private def Extension.hasFunCCAttr (ext : Extension) (declName : Name) : CoreM Bool := do
  return ext.getState (← getEnv) |>.funCC.contains declName

/--
Auxiliary function for registering `grind`, `grind!`, `grind?`, and `grind!?` attributes.
`grind!` is like `grind` but selects minimal indexable subterms.
The `grind?` and `grind!?` are aliases for `grind` and `grind!` which displays patterns using `logInfo`.
It is just a convenience for users.
-/
private def mkGrindAttr (attrName : Name) (minIndexable : Bool) (showInfo : Bool) (ext : Extension) (ref : Name := by exact decl_name%) : IO Unit :=
  registerBuiltinAttribute {
    ref  := ref
    name := match minIndexable, showInfo with
      | false, false => attrName
      | false, true  => attrName.appendAfter "?"
      | true,  false => attrName.appendAfter "!"
      | true,  true  => attrName.appendAfter "!?"
    descr :=
      let header := match minIndexable, showInfo with
        | false, false => s!"The `[{attrName}]` attribute is used to annotate declarations."
        | false, true  => s!"The `[{attrName}?]` attribute is identical to the `[{attrName}]` attribute, but displays inferred pattern information."
        | true,  false => s!"The `[{attrName}!]` attribute is used to annotate declarations, but selecting minimal indexable subterms."
        | true,  true  => s!"The `[{attrName}!?]` attribute is identical to the `[{attrName}!]` attribute, but displays inferred pattern information."
      header ++ s!"\
      \
      When applied to an equational theorem, `[{attrName} =]`, `[{attrName} =_]`, or `[{attrName} _=_]`\
      will mark the theorem for use in heuristic instantiations by the `{attrName}` tactic,
      using respectively the left-hand side, the right-hand side, or both sides of the theorem.\
      When applied to a function, `[{attrName} =]` automatically annotates the equational theorems associated with that function.\
      When applied to a theorem `[{attrName} ←]` will instantiate the theorem whenever it encounters the conclusion of the theorem
      (that is, it will use the theorem for backwards reasoning).\
      When applied to a theorem `[{attrName} →]` will instantiate the theorem whenever it encounters sufficiently many of the propositional hypotheses
      (that is, it will use the theorem for forwards reasoning).\
      \
      The attribute `[{attrName}]` by itself will effectively try `[{attrName} ←]` (if the conclusion is sufficient for instantiation) and then `[{attrName} →]`.\
      \
      The `grind` tactic utilizes annotated theorems to add instances of matching patterns into the local context during proof search.\
      For example, if a theorem `@[{attrName} =] theorem foo_idempotent : foo (foo x) = foo x` is annotated,\
      `grind` will add an instance of this theorem to the local context whenever it encounters the pattern `foo (foo x)`."
    applicationTime := .afterCompilation
    add := fun declName stx attrKind => MetaM.run' do
      recordExtraModUseFromDecl (isMeta := false) declName
      -- `[grind] def` should be allowed without `[expose]` so make body accessible unconditionally.
      -- When the body is not available (i.e. the def equations are private), the attribute will not
      -- be exported; see `ematchTheoremsExt.exportEntry?`.
      withoutExporting do
      match (← getAttrKindFromOpt stx) with
      | .symbol prio =>
        unless attrName == `grind do
          throwError "symbol priorities must be set using the default `[grind]` attribute"
        addSymbolPriorityAttr declName attrKind prio
      | .norm post inv =>
        unless attrName == `grind do
          throwError "normalizer must be set using the default `[grind]` attribute"
        addNormTheorem declName post inv attrKind
      | .unfold =>
        unless attrName == `grind do
          throwError "declaration to unfold must be set using the default `[grind]` attribute"
        unless (← addNormDeclToUnfold declName attrKind) do
          throwError "cannot mark declaration to be unfolded by `grind`"
      | .homo fallback =>
        unless attrName == `grind do
          throwError "homomorphism rules must be set using the default `[grind]` attribute"
        addHomoAttr declName attrKind fallback
      | .homoPred =>
        unless attrName == `grind do
          throwError "homomorphism predicates must be set using the default `[grind]` attribute"
        addHomoPredAttr declName attrKind
      | .cases eager => ext.addCasesAttr declName eager attrKind
      | .funCC => ext.addFunCCAttr declName attrKind
      | .ext => ext.addExtAttr declName attrKind
      | .ematch .user => throwInvalidUsrModifier
      | .ematch k => ext.addEMatchAttr declName attrKind k (← getGlobalSymbolPriorities) (minIndexable := minIndexable) (showInfo := showInfo)
      | .intro =>
        if let some info ← isCasesAttrPredicateCandidate? declName false then
          for ctor in info.ctors do
            ext.addEMatchAttr ctor attrKind (.default false) (← getGlobalSymbolPriorities) (minIndexable := minIndexable) (showInfo := showInfo)
        else
          throwError "invalid `[{attrName} intro]`, `{.ofConstName declName}` is not an inductive predicate"
      | .infer =>
        if let some declName ← isCasesAttrCandidate? declName false then
          ext.addCasesAttr declName false attrKind
          if let some info ← isInductivePredicate? declName then
            -- If it is an inductive predicate,
            -- we also add the constructors (intro rules) as E-matching rules
            for ctor in info.ctors do
              ext.addEMatchAttr ctor attrKind (.default false) (← getGlobalSymbolPriorities) (minIndexable := minIndexable) (showInfo := showInfo)
        else
          ext.addEMatchAttrAndSuggest stx declName attrKind (← getGlobalSymbolPriorities) (minIndexable := minIndexable) (showInfo := showInfo)
      | .inj => ext.addInjectiveAttr declName attrKind
    erase := fun declName => MetaM.run' do
      if showInfo then
        throwError "`[{attrName}?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `[{attrName}]` instead"
      if (← isCasesAttrCandidate declName false) then
        ext.eraseCasesAttr declName
      else if (← ext.isExtTheorem declName) then
        ext.eraseExtAttr declName
      else if (← ext.isInjectiveTheorem declName) then
        ext.eraseInjectiveAttr declName
      else if (← ext.hasFunCCAttr declName) then
        ext.eraseFunCCAttr declName
      else
        ext.eraseEMatchAttr declName
  }

/-
private def registerDefaultGrindAttr (minIndexable : Bool) (showInfo : Bool) : IO Unit :=
  mkGrindAttr `grind minIndexable showInfo

builtin_initialize
  registerDefaultGrindAttr (minIndexable := false) (showInfo := true)
  registerDefaultGrindAttr (minIndexable := false) (showInfo := false)
  registerDefaultGrindAttr (minIndexable := true) (showInfo := true)
  registerDefaultGrindAttr (minIndexable := true) (showInfo := false)
-/

abbrev ExtensionMap := Std.HashMap Name Extension

builtin_initialize extensionMapRef : IO.Ref ExtensionMap ← IO.mkRef {}

def getExtension? (attrName : Name) : CoreM (Option Extension) := do
  let ext? := (← extensionMapRef.get)[attrName]?
  if let some ext := ext? then
    recordExtraModUseFromDecl (isMeta := true) ext.ext.name
  return ext?

def registerAttr (attrName : Name) (ref : Name := by exact decl_name%) : IO Extension := do
  let ext ← mkExtension ref
  mkGrindAttr attrName (minIndexable := false) (showInfo := true) (ext := ext) (ref := ref)
  mkGrindAttr attrName (minIndexable := false) (showInfo := false) (ext := ext) (ref := ref)
  mkGrindAttr attrName (minIndexable := true) (showInfo := true) (ext := ext) (ref := ref)
  mkGrindAttr attrName (minIndexable := true) (showInfo := false) (ext := ext) (ref := ref)
  extensionMapRef.modify fun map => map.insert attrName ext
  return ext

builtin_initialize grindExt : Extension ← registerAttr `grind

/--
Extension backing the `@[lia]` attribute. It uses the same recording mechanism as `@[grind]`
(see `registerAttr`), but provides a separate, smaller E-matching lemma set that the `lia`
tactic instantiates (e.g. `Nat.max_def`), without enabling the full `@[grind]` set.
-/
builtin_initialize liaExt : Extension ← registerAttr `lia

/-- Returns `true` is `declName` is a builtin split or has been tagged with `[grind]` attribute. -/
def isGlobalSplit (declName : Name) : CoreM Bool := do
  let s := grindExt.getState (← getEnv)
  return s.casesTypes.isSplit declName

end Lean.Meta.Grind
