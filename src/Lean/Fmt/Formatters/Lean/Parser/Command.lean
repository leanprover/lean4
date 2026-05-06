/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Parser.Command
import Lean.Fmt.FmtM.CommonFormatters
import Lean.Fmt.Formatters.Lean.Parser.Term
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Command.eoi]
public def fmtEoi : Fmt := fun _ => return empty

@[builtin_fmt Lean.Parser.Term.quot]
public def fmtTermQuot : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.moduleDoc]
public def fmtModuleDoc : Fmt := fmtRawAsInSource -- TODO once verso docstrings are fixed

@[builtin_fmt Lean.Parser.Command.private]
public def fmtPrivate : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.public]
public def fmtPublic : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.protected]
public def fmtProtected : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.meta]
public def fmtMeta : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.noncomputable]
public def fmtNoncomputable : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.unsafe]
public def fmtUnsafe : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.partial]
public def fmtPartial : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.nonrec]
public def fmtNonrec : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.declId]
public def fmtDeclId : Fmt := fun
  | `(Parser.Command.declId| $declId:ident $[.{%$lbTk? $universeIds?:ident,* }%$rbTk?]?) => do
    let declId ← fmt declId
    let universeAnnotation? ← fmtUniverseAnnotation? lbTk? universeIds? rbTk?
    return Layouts.atomic #[
      declId,
      universeAnnotation?
    ]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.namedPrio]
public def fmtNamedPrio : Fmt := fun
  | `(Parser.Command.namedPrio| (%$lbTk priority%$prioTk :=%$colonEqTk $prio:prio )%$rbTk) => do
    fmtNamedArgumentTerm lbTk prioTk colonEqTk prio rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.abbrev]
public def fmtAbbrev : Fmt := fun
  | `(Parser.Command.abbrev|
      abbrev%$abbrevTk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]? :=%$colonEqTk
        $declBody:term
      $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) => do
    fmtAssignmentDeclaration abbrevTk none declId binders typeAscriptionTk? type? colonEqTk declBody
      terminationSuffix whereDecls?
  | `(Parser.Command.abbrev|
      abbrev%$abbrevTk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]?
        $matchAlts:matchAlts
      $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) => do
    fmtMatchDeclaration abbrevTk none declId binders typeAscriptionTk? type? matchAlts
      terminationSuffix whereDecls?
  | `(Parser.Command.abbrev|
      abbrev%$abbrevTk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]? where%$whereTk
        $fields:structInstField;*
      $[$whereDecls?:whereDecls]?) => do
    fmtWhereDeclaration abbrevTk none declId binders typeAscriptionTk? type? whereTk fields
      whereDecls?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.derivingClass]
public def fmtDerivingClass : Fmt := fun
  | `(Parser.Command.derivingClass| $[@[%$lbTk? expose%$exposeTk? ]%$rbTk? ]? $classTerm:term) => do
    let lbTk? ← fmt? lbTk?
    let exposeTk? ← fmt? exposeTk?
    let rbTk? ← fmt? rbTk?
    let classTerm ← fmt classTerm
    let exposeAttribute := Layouts.bracketed lbTk? exposeTk? rbTk? .dense
    return Layouts.horizontalOrVertical #[exposeAttribute, classTerm]
  | _ =>
    throw .partialFormatter

public def fmtDerivingSuffix
    (derivingTk? : Option Syntax)
    (classes? : Option (Syntax.TSepArray ``Parser.Command.derivingClass ","))
    : FmtM TaggedDoc := do
  let derivingTk? ← fmt? derivingTk?
  let classes := classes?.getD ⟨#[]⟩
  let classes ← fmtTSepArray classes
  return Layouts.keywordPrefixedSepFill derivingTk? classes .nonSticky

@[builtin_fmt Lean.Parser.Command.definition]
public def fmtDefinition : Fmt := fun
  | `(Parser.Command.definition|
      def%$defTk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]? :=%$colonEqTk
        $declBody:term
      $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?
      $[deriving%$derivingTk? $classes?:derivingClass,*]?) => do
    let decl ←
      fmtAssignmentDeclaration defTk none declId binders typeAscriptionTk? type? colonEqTk declBody
        terminationSuffix whereDecls?
    let «deriving» ← fmtDerivingSuffix derivingTk? classes?
    return Layouts.lines #[decl, «deriving»]
  | `(Parser.Command.definition|
      def%$defTk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]?
        $matchAlts:matchAlts
      $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?
      $[deriving%$derivingTk? $classes?:derivingClass,*]?) => do
    let decl ←
      fmtMatchDeclaration defTk none declId binders typeAscriptionTk? type? matchAlts
        terminationSuffix whereDecls?
    let «deriving» ← fmtDerivingSuffix derivingTk? classes?
    return Layouts.lines #[decl, «deriving»]
  | `(Parser.Command.definition|
      def%$defTk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]? where%$whereTk
        $fields:structInstField;*
      $[$whereDecls?:whereDecls]?
      $[deriving%$derivingTk? $classes?:derivingClass,*]?) => do
    let decl ←
      fmtWhereDeclaration defTk none declId binders typeAscriptionTk? type? whereTk fields
        whereDecls?
    let «deriving» ← fmtDerivingSuffix derivingTk? classes?
    return Layouts.lines #[decl, «deriving»]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.theorem]
public def fmtTheorem : Fmt := fun
  | `(Parser.Command.theorem|
      theorem%$theoremTk $declId:declId $binders* :%$typeAscriptionTk $type:term :=%$colonEqTk
        $declBody:term
      $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) => do
    fmtAssignmentDeclaration theoremTk none declId binders typeAscriptionTk type colonEqTk declBody
      terminationSuffix whereDecls?
  | `(Parser.Command.theorem|
      theorem%$theoremTk $declId:declId $binders* :%$typeAscriptionTk $type:term
        $matchAlts:matchAlts
      $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) => do
    fmtMatchDeclaration theoremTk none declId binders typeAscriptionTk type matchAlts
      terminationSuffix whereDecls?
  | `(Parser.Command.theorem|
      theorem%$theoremTk $declId:declId $binders* :%$typeAscriptionTk $type:term  where%$whereTk
        $fields:structInstField;*
      $[$whereDecls?:whereDecls]?) => do
    fmtWhereDeclaration theoremTk none declId binders typeAscriptionTk type whereTk fields
      whereDecls?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.opaque]
public def fmtOpaque : Fmt := fun
  | `(Parser.Command.opaque|
      opaque%$opaqueTk $declId:declId $binders* :%$typeAscriptionTk $type:term :=%$colonEqTk
        $declBody:term
      $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) => do
    fmtAssignmentDeclaration opaqueTk none declId binders typeAscriptionTk type colonEqTk declBody
      terminationSuffix whereDecls?
  | `(Parser.Command.opaque|
      opaque%$opaqueTk $declId:declId $binders* :%$typeAscriptionTk $type:term) => do
    fmtDeclarationSignature #[opaqueTk] none declId binders typeAscriptionTk type
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.instance]
public def fmtInstance : Fmt := fun
  | `(Parser.Command.instance|
      $attrKind:attrKind instance%$instanceTk $[$namedPrio?:namedPrio]? $[$declId?:declId]? $binders* :%$typeAscriptionTk $type:term :=%$colonEqTk
        $declBody:term
      $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) => do
    let attrKind ← fmt attrKind
    let decl ←
      fmtAssignmentDeclaration instanceTk namedPrio? declId? binders typeAscriptionTk type colonEqTk
        declBody terminationSuffix whereDecls?
    return Layouts.spacedAtomic #[attrKind, decl]
  | `(Parser.Command.instance|
      $attrKind:attrKind instance%$instanceTk $[$namedPrio?:namedPrio]? $[$declId?:declId]? $binders* :%$typeAscriptionTk $type:term
        $matchAlts:matchAlts
      $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) => do
    let attrKind ← fmt attrKind
    let decl ←
      fmtMatchDeclaration instanceTk namedPrio? declId? binders typeAscriptionTk type matchAlts
        terminationSuffix whereDecls?
    return Layouts.spacedAtomic #[attrKind, decl]
  | `(Parser.Command.instance|
      $attrKind:attrKind instance%$instanceTk $[$namedPrio?:namedPrio]? $[$declId?:declId]? $binders* :%$typeAscriptionTk $type:term  where%$whereTk
        $fields:structInstField;*
      $[$whereDecls?:whereDecls]?) => do
    let attrKind ← fmt attrKind
    let decl ←
      fmtWhereDeclaration instanceTk namedPrio? declId? binders typeAscriptionTk type whereTk fields
        whereDecls?
    return Layouts.spacedAtomic #[attrKind, decl]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.axiom]
public def fmtAxiom : Fmt := fun
  | `(Parser.Command.axiom|
      axiom%$axiomTk $declId:declId $binders* :%$typeAscriptionTk $type:term) => do
    fmtDeclarationSignature #[axiomTk] none declId binders typeAscriptionTk type
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.example]
public def fmtExample : Fmt := fun
  | `(Parser.Command.example|
      example%$exampleTk $binders* $[:%$typeAscriptionTk? $type?:term]? :=%$colonEqTk
        $declBody:term
      $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) => do
    fmtAssignmentDeclaration exampleTk none none binders typeAscriptionTk? type? colonEqTk declBody
      terminationSuffix whereDecls?
  | `(Parser.Command.example|
      example%$exampleTk $binders* $[:%$typeAscriptionTk? $type?:term]?
        $matchAlts:matchAlts
      $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) => do
    fmtMatchDeclaration exampleTk none none binders typeAscriptionTk? type? matchAlts
      terminationSuffix whereDecls?
  | `(Parser.Command.example|
      example%$exampleTk $binders* $[:%$typeAscriptionTk? $type?:term]? where%$whereTk
        $fields:structInstField;*
      $[$whereDecls?:whereDecls]?) => do
    fmtWhereDeclaration exampleTk none none binders typeAscriptionTk? type? whereTk fields
      whereDecls?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.recallCmd]
public def fmtRecallCmd : Fmt := fun
  | `(Parser.Command.recallCmd|
      $[$docComment?:docComment]?
      recall%$recallTk $id:ident $binders* $[:%$typeAscriptionTk? $type?:term]? :=%$colonEqTk
        $declBody:term) => do
    fmtAssignmentDeclaration recallTk none id binders typeAscriptionTk? type? colonEqTk declBody
      none none
  | `(Parser.Command.recallCmd|
      $[$docComment?:docComment]?
      recall%$recallTk $id:ident $binders* $[:%$typeAscriptionTk? $type?:term]?
        $matchAlts:matchAlts) => do
    fmtMatchDeclaration recallTk none id binders typeAscriptionTk? type? matchAlts none none
  | `(Parser.Command.recallCmd|
      $[$docComment?:docComment]?
      recall%$recallTk $id:ident $binders* $[:%$typeAscriptionTk? $type?:term]? where%$whereTk
        $fields:structInstField;*) => do
    fmtWhereDeclaration recallTk none id binders typeAscriptionTk? type? whereTk fields none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.recallQuestionCmd]
public def fmtRecallQuestionCmd : Fmt := fun
  | `(Parser.Command.recallQuestionCmd| recall?%$recallTk $id:ident) => do
    let recallTk ← fmt recallTk
    let id ← fmt id
    return Layouts.pseudoApplication #[recallTk, id]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.ctor]
public def fmtCtor : Fmt := fun
  | `(Parser.Command.ctor|
      $[$outerDocComment?:docComment]?
      |%$altTk $declModifiers:declModifiers
        $id:ident $binders* $[:%$typeAscriptionTk? $type?:term]?) => do
    let outerDocComment? ← fmt? outerDocComment?
    let altTk ← fmt altTk
    let signature ← fmtGlobalSignature id binders typeAscriptionTk? type?
    let decl ← fmtDeclWithDeclModifiers declModifiers signature
    let ctorDecl := nested <| Layouts.spacedAtomic #[altTk, decl]
    return Layouts.lines #[outerDocComment?, ctorDecl]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.computedField]
public def fmtComputedField : Fmt := fun
  | `(Lean.Parser.Command.computedField|
      $declModifiers:declModifiers $id:ident :%$typeAscriptionTk $type
        $matchAlts:matchAlts) => do
    let signature ← fmtGlobalSignature id #[] typeAscriptionTk type
    let matchAlts ← fmt matchAlts
    let decl := Layouts.matchDeclaration signature matchAlts
    fmtDeclWithDeclModifiers declModifiers decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.computedFields]
public def fmtComputedFields : Fmt := fun
  | `(Parser.Command.computedFields| with%$withTk $fields:computedField*) => do
    let withTkDoc ← fmt withTk
    let withTkTrailingDoc ← fmtTrailingWithRetainedNewlinesAndComments withTk
    let fieldsDoc ← fmtArrayWithRetainedIntermediateNewlinesAndComments fields
    return nested <| Layouts.retainedWhitespace #[withTkDoc, withTkTrailingDoc, fieldsDoc]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.optDeriving]
public def fmtOptDeriving : Fmt := fun
  | `(Parser.Command.optDeriving|
      $[deriving%$derivingTk? $classes?:derivingClass,*]?) =>
    fmtDerivingSuffix derivingTk? classes?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.monotonicityBy]
public def fmtMonotonicityBy : Fmt := fun
  | `(Parser.Command.monotonicityBy| monotonicity_by%$monotonicityByTk $seq:tacticSeq) => do
    let monotonicityByTk ← fmt monotonicityByTk
    let seq ← fmt seq
    return Layouts.keywordPrefixedSeq monotonicityByTk seq .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.inductive]
public def fmtInductive : Fmt := fun
  | `(Parser.Command.inductive|
      inductive%$inductiveTk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]?
        $ctors*
        $[$computedFields?:computedFields]?
        $optDeriving:optDeriving
        $[$monotonicityBy?:monotonicityBy]?) =>
    fmtInductiveLike #[inductiveTk] declId binders typeAscriptionTk? type? none ctors
      computedFields? optDeriving monotonicityBy?
  | `(Parser.Command.inductive|
      -- Anti-quotations only match on `Syntax.node`, so the `:=%$sepTk` actually matches both
      -- `:=` and `where` of the `optional (symbol " :=" <|> " where")` parser of `inductive`.
      inductive%$inductiveTk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]? :=%$sepTk
        $ctors*
        $[$computedFields?:computedFields]?
        $optDeriving:optDeriving
        $[$monotonicityBy?:monotonicityBy]?) =>
    fmtInductiveLike #[inductiveTk] declId binders typeAscriptionTk? type? sepTk ctors
      computedFields? optDeriving monotonicityBy?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.coinductive]
public def fmtCoinductive : Fmt := fun
  | `(Parser.Command.coinductive|
      coinductive%$coinductiveTk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]?
        $ctors*
        $[$computedFields?:computedFields]?
        $optDeriving:optDeriving
        $[$monotonicityBy?:monotonicityBy]?) =>
    fmtInductiveLike #[coinductiveTk] declId binders typeAscriptionTk? type? none ctors
      computedFields? optDeriving monotonicityBy?
  | `(Parser.Command.coinductive|
      -- Anti-quotations only match on `Syntax.node`, so the `:=%$sepTk` actually matches both
      -- `:=` and `where` of the `optional (symbol " :=" <|> " where")` parser of `coinductive`.
      coinductive%$coinductiveTk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]? :=%$sepTk
        $ctors*
        $[$computedFields?:computedFields]?
        $optDeriving:optDeriving
        $[$monotonicityBy?:monotonicityBy]?) =>
    fmtInductiveLike #[coinductiveTk] declId binders typeAscriptionTk? type? sepTk ctors
      computedFields? optDeriving monotonicityBy?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.classInductive]
public def fmtClassInductive : Fmt := fun
  | `(Parser.Command.classInductive|
      class%$classTk inductive%$inductiveTk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]?
        $ctors*
        $optDeriving:optDeriving) =>
    fmtInductiveLike #[classTk, inductiveTk] declId binders typeAscriptionTk? type? none ctors none
      optDeriving none
  | `(Parser.Command.classInductive|
      -- Anti-quotations only match on `Syntax.node`, so the `:=%$sepTk` actually matches both
      -- `:=` and `where` of the `optional (symbol " :=" <|> " where")` parser of `class inductive`.
      class%$classTk inductive%$inductiveTk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]? :=%$sepTk
        $ctors*
        $optDeriving:optDeriving) =>
    fmtInductiveLike #[classTk, inductiveTk] declId binders typeAscriptionTk? type? sepTk ctors none
      optDeriving none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.structureTk]
public def fmtStructureTk : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.classTk]
public def fmtClassTk : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.structParent]
public def fmtStructParent : Fmt := fun
  | `(Parser.Command.structParent| $[$toParentId?:ident :%$typeAscriptionTk? ]? $type:term) => do
    let toParentId? ← fmt? toParentId?
    let typeAscriptionTk? ← fmt? typeAscriptionTk?
    let type ← fmt type
    return Layouts.globalSignature #[toParentId?] #[] typeAscriptionTk? type
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.extends]
public def fmtExtends : Fmt := fun
  -- The grammar of `Parser.Command.extends` allows a `Term.optType` at the end of `extends`,
  -- but this is kept around purely for producing an elaboration error for a form of the syntax
  -- that has since been removed. We do not attempt to format this legacy syntax that always
  -- produces an elaboration error.
  | `(Parser.Command.extends| extends%$extendsTk $structParents:structParent,*) => do
    let extendsTk ← fmt extendsTk
    let structParents ← fmtTSepArray structParents
    return Layouts.keywordPrefixedSepFill extendsTk structParents .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.structCtor]
public def fmtStructCtor : Fmt := fun
  | `(Parser.Command.structCtor|
      $declModifiers:declModifiers $ctorId:ident $binderUpdates* ::%$ctorTk) => do
    let signature ← fmtGlobalSignature ctorId binderUpdates none none
    let ctorTk ← fmt ctorTk
    let decl := Layouts.postfixOperator (hardNested signature) ctorTk .withSpacing
    fmtDeclWithDeclModifiers declModifiers decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.structExplicitBinder]
public def fmtStructExplicitBinder : Fmt := fun
  | `(Parser.Command.structExplicitBinder|
      $declModifiers:declModifiers
      (%$lbTk $ids:ident* $signature:optDeclSig $[$tacticOrDefault?]? )%$rbTk) => do
    -- We expand `structExplicitBinder` in two stages like this because inlining it confuses the
    -- anti-quotation parser.
    let `(Parser.Command.optDeclSig| $binders* $[:%$typeAscriptionTk? $type?:term]?) := signature
      | throw .partialFormatter
    let binder ←
      fmtBinder #[lbTk] ids binders typeAscriptionTk? type? tacticOrDefault? #[rbTk]
        (kind := .global)
    fmtDeclWithDeclModifiers declModifiers binder
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.structImplicitBinder]
public def fmtStructImplicitBinder : Fmt := fun
  | `(Parser.Command.structImplicitBinder|
      $declModifiers:declModifiers
      {%$lbTk $ids:ident* $signature:declSig }%$rbTk) => do
    -- We expand `structImplicitBinder` in two stages like this because inlining it confuses the
    -- anti-quotation parser.
    let `(Parser.Command.declSig| $binders* :%$typeAscriptionTk $type:term) := signature
      | throw .partialFormatter
    let binder ← fmtBinder #[lbTk] ids binders typeAscriptionTk type none #[rbTk] (kind := .global)
    fmtDeclWithDeclModifiers declModifiers binder
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.structInstBinder]
public def fmtStructInstBinder : Fmt := fun
  | `(Parser.Command.structInstBinder|
      $declModifiers:declModifiers
      [%$lbTk $ids:ident* $signature:declSig ]%$rbTk) => do
    -- We expand `structInstBinder` in two stages like this because inlining it confuses the
    -- anti-quotation parser.
    let `(Parser.Command.declSig| $binders* :%$typeAscriptionTk $type:term) := signature
      | throw .partialFormatter
    let binder ← fmtBinder #[lbTk] ids binders typeAscriptionTk type none #[rbTk] (kind := .global)
    fmtDeclWithDeclModifiers declModifiers binder
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.structSimpleBinder]
public def fmtStructSimpleBinder : Fmt := fun
  | `(Parser.Command.structSimpleBinder|
      $declModifiers:declModifiers
      $id:ident $binders* $[:%$typeAscriptionTk? $type?:term]? $[$tacticOrDefault?]?) => do
    let binder ←
      fmtBinder #[] #[id] binders typeAscriptionTk? type? tacticOrDefault? #[] (kind := .global)
    fmtDeclWithDeclModifiers declModifiers binder
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.structure]
public def fmtStructure : Fmt := fun
  | `(Parser.Command.structure|
      $tk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]? $[$extends?:extends]? $[where%$whereTk?
        $[$structCtor?:structCtor]?
          $structFields?*]?
      $optDeriving:optDeriving) =>
    fmtStructureLike tk declId binders typeAscriptionTk? type? extends? whereTk? structCtor?.join
      structFields? optDeriving
  | `(Parser.Command.structure|
      $tk $declId:declId $binders* $[:%$typeAscriptionTk? $type?:term]? $[$extends?:extends]?
        $[:=%$colonEqTk? $[$structCtor?:structCtor]?
          $structFields?*]?
      $optDeriving:optDeriving) =>
    fmtStructureLike tk declId binders typeAscriptionTk? type? extends? colonEqTk? structCtor?.join
      structFields? optDeriving
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.declaration]
public def fmtDeclaration : Fmt := fun
  | `(Parser.Command.declaration| $declModifiers:declModifiers $decl) => do
    let decl ← fmt decl
    fmtDeclWithDeclModifiers declModifiers decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.eraseAttr]
public def fmtEraseAttr : Fmt := fun
  | `(Parser.Command.eraseAttr| -%$minusTk $attrName:ident) => do
    let minusTk ← fmt minusTk
    let attrName ← fmt attrName
    return Layouts.prefixOperator minusTk attrName .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.attribute]
public def fmtAttributeCmd : Fmt := fun
  | `(Parser.Command.attribute| attribute%$attributeTk [%$lbTk $attrs,* ]%$rbTk $declIds:ident*) =>
    do
      let attributeTk ← fmt attributeTk
      let lbTk ← fmt lbTk
      let attrs ← fmtTSepArray attrs
      let rbTk ← fmt rbTk
      let declIds ← fmtArray declIds
      let attrBody := Layouts.collection lbTk attrs rbTk { unindentedRb := false }
      let declIds := Layouts.fill declIds
      return Layouts.blocks #[attributeTk, attrBody, declIds]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.section]
public def fmtSection : Fmt := fun
  | `(Parser.Command.section| $[@[%$exposeLbTk? expose%$exposeTk? ]%$exposeRbTk? ]? $[public%$publicTk?]? $[noncomputable%$noncomputableTk?]? $[meta%$metaTk?]? section%$sectionTk $[$id?]?) =>
    do
      let exposeLbTk? ← fmt? exposeLbTk?
      let exposeTk? ← fmt? exposeTk?
      let exposeRbTk? ← fmt? exposeRbTk?
      let publicTk? ← fmt? publicTk?
      let noncomputableTk? ← fmt? noncomputableTk?
      let metaTk? ← fmt? metaTk?
      let sectionTk ← fmt sectionTk
      let exposeAttribute := Layouts.bracketed exposeLbTk? exposeTk? exposeRbTk? .dense
      let tks := Layouts.spacedAtomic #[publicTk?, noncomputableTk?, metaTk?, sectionTk]
      let id? ← fmt? id?
      let sectionDecl := Layouts.pseudoApplication #[tks, id?]
      return Layouts.horizontalOrVertical #[exposeAttribute, sectionDecl]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.namespace]
public def fmtNamespace : Fmt := fun
  | `(Parser.Command.namespace| namespace%$namespaceTk $id:ident) => do
    let namespaceTk ← fmt namespaceTk
    let id ← fmt id
    return Layouts.pseudoApplication #[namespaceTk, id]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.end]
public def fmtEnd : Fmt := fun
  | `(Parser.Command.end| end%$endTk $[$id?:ident]?) => do
    let endTk ← fmt endTk
    let id? ← fmt? id?
    return Layouts.pseudoApplication #[endTk, id?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.variable]
public def fmtVariable : Fmt := fun
  | `(Parser.Command.variable| variable%$variableTk $binders:bracketedBinder*) =>
    fmtGlobalSignature variableTk binders none none
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.set_option]
public def fmtSetOption : Fmt := fun
  | `(Parser.Command.set_option| set_option%$setOptionTk $optionId:ident $optionValue) => do
    let setOptionTk ← fmt setOptionTk
    let optionId ← fmt optionId
    let optionValue ← fmt optionValue
    return Layouts.pseudoApplication #[setOptionTk, optionId, optionValue]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.in]
public def fmtIn : Fmt := fun
  | `($cmd₁ in%$inTk $cmd₂) => do
    let cmd₁ ← fmt cmd₁
    let inTk ← fmt inTk
    let cmd₂ ← fmt cmd₂
    return Layouts.lines #[Layouts.spacedAtomic #[cmd₁, inTk], cmd₂]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.universe]
public def fmtUniverse : Fmt := fun
  | `(Parser.Command.universe| universe%$universeTk $ids*) => do
    let universeTk ← fmt universeTk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[universeTk] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.export]
public def fmtExport : Fmt := fun
  | `(Parser.Command.export| export%$exportTk $namespaceId:ident (%$lbTk $exportedIds:ident* )%$rbTk ) =>
    do
      let exportTk ← fmt exportTk
      let namespaceId ← fmt namespaceId
      let lbTk ← fmt lbTk
      let exportedIds ← fmtArray exportedIds
      let rbTk ← fmt rbTk
      let exportedIds := Layouts.fill exportedIds
      let exported := Layouts.parens lbTk exportedIds rbTk
      return Layouts.pseudoApplication #[exportTk, namespaceId, exported]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.init_quot]
public def fmtInitQuot : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.addDocString]
public def fmtAddDocString : Fmt := fun
  | `(Parser.Command.addDocString| $docComment:docComment add_decl_doc%$addDeclDocTk $id:ident) =>
    do
      let docComment ← fmt docComment
      let addDeclDocTk ← fmt addDeclDocTk
      let id ← fmt id
      let addDeclDoc := Layouts.pseudoApplication #[addDeclDocTk, id]
      return Layouts.lines #[docComment, addDeclDoc]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.deriving]
public def fmtDeriving : Fmt
  | `(Parser.Command.deriving|
      deriving%$derivingTk $[noncomputable%$noncomputableTk?]? instance%$instanceTk $classes:derivingClass,* for%$forTk $terms:term,*) =>
    do
      let derivingTk ← fmt derivingTk
      let noncomputableTk? ← fmt? noncomputableTk?
      let instanceTk ← fmt instanceTk
      let classes ← fmtTSepArray classes
      let forTk ← fmt forTk
      let terms ← fmtTSepArray terms
      let tks := Layouts.spacedAtomic #[derivingTk, noncomputableTk?, instanceTk]
      let lhs := Layouts.keywordPrefixedSepFill tks classes .nonSticky
      let «for» := Layouts.keywordPrefixedSepFill forTk terms .sticky
      return Layouts.pseudoApplication #[lhs, «for»]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.openRenamingItem]
public def fmtOpenRenamingItem : Fmt
  | `(Parser.Command.openRenamingItem| $fromDecl:ident →%$arrowTk $toDecl:ident) => do
    let fromDecl ← fmt fromDecl
    let arrowTk ← fmt arrowTk
    let toDecl ← fmt toDecl
    return Layouts.infixOperator (format := .dense) #[fromDecl, arrowTk, toDecl]
  | _ =>
    throw .partialFormatter

public def fmtOpenDecl (openTk : Syntax) (decl : TSyntax ``Parser.Command.openDecl)
    : FmtM TaggedDoc := do
  match decl with
  | `(Parser.Command.openHiding| $id:ident hiding%$hidingTk $hiddenDecls:ident*) =>
    let openTk ← fmt openTk
    let id ← fmt id
    let lhs := Layouts.pseudoApplication #[openTk, id]
    let hidingTk ← fmt hidingTk
    let hiddenDecls ← fmtArray hiddenDecls
    let hiddenDecls := Layouts.fill hiddenDecls
    let «hiding» := Layouts.keywordPrefixedTerm hidingTk hiddenDecls
    return Layouts.pseudoApplication #[lhs, «hiding»]
  | `(Parser.Command.openRenaming| $id:ident renaming%$renamingTk $items:openRenamingItem,*) => do
    let openTk ← fmt openTk
    let id ← fmt id
    let lhs := Layouts.pseudoApplication #[openTk, id]
    let renamingTk ← fmt renamingTk
    let items ← fmtTSepArray items
    let items := Layouts.sepArray items <| .joinUsingSep none nl
    let «renaming» := Layouts.keywordPrefixedTerm renamingTk items
    return Layouts.pseudoApplication #[lhs, «renaming»]
  | `(Parser.Command.openOnly| $id:ident (%$lbTk $decls:ident* )%$rbTk) =>
    let openTk ← fmt openTk
    let id ← fmt id
    let lbTk ← fmt lbTk
    let decls := ← fmtArray decls
    let rbTk ← fmt rbTk
    let decls := Layouts.fill decls
    let bracketedDecls := Layouts.parens lbTk decls rbTk
    return Layouts.pseudoApplication #[openTk, id, bracketedDecls]
  | `(Parser.Command.openSimple| $ids:ident*) =>
    let openTk ← fmt openTk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[openTk] ++ ids
  | `(Parser.Command.openScoped| scoped%$scopedTk $ids*) =>
    let openTk ← fmt openTk
    let scopedTk ← fmt scopedTk
    let tks := Layouts.spacedAtomic #[openTk, scopedTk]
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[tks] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.open]
public def fmtOpen : Fmt := fun
  | `(Parser.Command.open| open%$openTk $decl:openDecl) => fmtOpenDecl openTk decl
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.open]
public def fmtTermOpen : Fmt := fun
  | `(Parser.Term.open| open%$openTk $decl:openDecl in%$inTk $body:term) => do
    let openDecl ← fmtOpenDecl openTk decl
    let inTk ← fmt inTk
    let body ← fmt body
    return Layouts.keywordSeparated openDecl inTk body {
      allowFlattening := false
      nestedRhs := false
    }
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.open]
public def fmtTacticOpen : Fmt := fun
  | `(Parser.Tactic.open| open%$openTk $decl:openDecl in%$inTk $tacs:tacticSeq) => do
    let openDecl ← fmtOpenDecl openTk decl
    let inTk ← fmt inTk
    let tacs ← fmt tacs
    let indentedVariant :=
      Layouts.keywordSeparated openDecl inTk tacs { allowFlattening := false, nestedRhs := true }
    let dedentedVariant :=
      Layouts.keywordSeparated openDecl inTk tacs { allowFlattening := false, nestedRhs := false }
    return pseudoDedented indentedVariant dedentedVariant
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.set_option]
public def fmtTermSetOption : Fmt := fun
  | `(Parser.Term.set_option| set_option%$setOptionTk $optionId:ident $optionValue in%$inTk $body:term) =>
    do
      let setOptionTk ← fmt setOptionTk
      let optionId ← fmt optionId
      let optionValue ← fmt optionValue
      let setOption := Layouts.pseudoApplication #[setOptionTk, optionId, optionValue]
      let inTk ← fmt inTk
      let body ← fmt body
      let indentedVariant :=
        Layouts.keywordSeparated setOption inTk body { allowFlattening := false, nestedRhs := true }
      let dedentedVariant :=
        Layouts.keywordSeparated setOption inTk body {
          allowFlattening := false
          nestedRhs := false
        }
      return pseudoDedented indentedVariant dedentedVariant
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.set_option]
public def fmtTacticSetOption : Fmt := fun
  | `(Parser.Tactic.set_option| set_option%$setOptionTk $optionId:ident $optionValue in%$inTk $tacs:tacticSeq) =>
    do
      let setOptionTk ← fmt setOptionTk
      let optionId ← fmt optionId
      let optionValue ← fmt optionValue
      let setOption := Layouts.pseudoApplication #[setOptionTk, optionId, optionValue]
      let inTk ← fmt inTk
      let tacs ← fmt tacs
      return Layouts.keywordSeparated setOption inTk tacs {
        allowFlattening := false
        nestedRhs := false
      }
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.exit]
public def fmtExit : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.where]
public def fmtWhereCmd : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.version]
public def fmtVersion : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.dumpAsyncEnvState]
public def fmtDumpAsyncEnvState : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.showDeprecatedModules]
public def fmtShowDeprecatedModules : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.unlock_limits]
public def fmtUnlockLimits : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.import]
public def fmtImport : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.checkAssertions]
public def fmtCheckAssertions : Fmt := fun
  | `(Parser.Command.checkAssertions| #check_assertions%$checkAssertionsTk $[!%$bangTk?]?) => do
    let checkAssertionsTk ← fmt checkAssertionsTk
    let bangTk? ← fmt? bangTk?
    return Layouts.atomic #[checkAssertionsTk, bangTk?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.precheckedQuot]
public def fmtTermPrecheckedQuot : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.check]
public def fmtCheck : Fmt := fun
  | `(Parser.Command.check| #check%$checkTk $t:term) => do
    let checkTk ← fmt checkTk
    let t ← fmt t
    return Layouts.pseudoApplication #[checkTk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.check_failure]
public def fmtCheckFailure : Fmt := fun
  | `(Parser.Command.check_failure| #check_failure%$checkFailureTk $t:term) => do
    let checkFailureTk ← fmt checkFailureTk
    let t ← fmt t
    return Layouts.pseudoApplication #[checkFailureTk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.importPath]
public def fmtImportPath : Fmt := fun
  | `(Parser.Command.importPath| #import_path%$importPathTk $id:ident) => do
    let importPathTk ← fmt importPathTk
    let id ← fmt id
    return Layouts.pseudoApplication #[importPathTk, id]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.assertNotExists]
public def fmtAssertNotExists : Fmt := fun
  | `(Parser.Command.assertNotExists| assert_not_exists%$assertNotExistsTk $ids:ident*) => do
    let assertNotExistsTk ← fmt assertNotExistsTk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[assertNotExistsTk] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.assertNotImported]
public def fmtAssertNotImported : Fmt := fun
  | `(Parser.Command.assertNotImported| assert_not_imported%$assertNotImportedTk $ids:ident*) => do
    let assertNotImportedTk ← fmt assertNotImportedTk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[assertNotImportedTk] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.eval]
public def fmtEval : Fmt := fun
  | `(Parser.Command.eval| #eval%$evalTk $t:term) => do
    let evalTk ← fmt evalTk
    let t ← fmt t
    return Layouts.pseudoApplication #[evalTk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.evalBang]
public def fmtEvalBang : Fmt := fun
  | `(Parser.Command.evalBang| #eval!%$evalBangTk $t:term) => do
    let evalBangTk ← fmt evalBangTk
    let t ← fmt t
    return Layouts.pseudoApplication #[evalBangTk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.synth]
public def fmtSynth : Fmt := fun
  | `(Parser.Command.synth| #synth%$synthTk $t:term) => do
    let synthTk ← fmt synthTk
    let t ← fmt t
    return Layouts.pseudoApplication #[synthTk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.print]
public def fmtPrint : Fmt := fun
  | `(Parser.Command.print| #print%$printTk $arg) => do
    let printTk ← fmt printTk
    let arg ← fmt arg
    return Layouts.pseudoApplication #[printTk, arg]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.genInjectiveTheorems]
public def fmtGenInjectiveTheorems : Fmt := fun
  | `(Parser.Command.genInjectiveTheorems| gen_injective_theorems%%$genInjectiveTheoremsTk $id:ident) =>
    do
      let genInjectiveTheoremsTk ← fmt genInjectiveTheoremsTk
      let id ← fmt id
      return Layouts.pseudoApplication #[genInjectiveTheoremsTk, id]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.include]
public def fmtInclude : Fmt := fun
  | `(Parser.Command.include| include%$includeTk $ids:ident*) => do
    let includeTk ← fmt includeTk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[includeTk] ++ ids
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.omit]
public def fmtOmit : Fmt := fun
  | `(Parser.Command.omit| omit%$omitTk $[$omitted]*) => do
    let omitTk ← fmt omitTk
    let omitted ← fmtArray omitted
    return Layouts.pseudoApplication <| #[omitTk] ++ omitted
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.printSig]
public def fmtPrintSig : Fmt := fun
  | `(Parser.Command.printSig| #print%$printTk sig%$sigTk $id:ident) => do
    let printTk ← fmt printTk
    let sigTk ← fmt sigTk
    let keywords := Layouts.spacedAtomic #[printTk, sigTk]
    let id ← fmt id
    return Layouts.pseudoApplication #[keywords, id]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.printAxioms]
public def fmtPrintAxioms : Fmt := fun
  | `(Parser.Command.printAxioms| #print%$printTk axioms%$axiomsTk $id:ident) => do
    let printTk ← fmt printTk
    let axiomsTk ← fmt axiomsTk
    let keywords := Layouts.spacedAtomic #[printTk, axiomsTk]
    let id ← fmt id
    return Layouts.pseudoApplication #[keywords, id]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.printEqns]
public def fmtPrintEqns : Fmt := fun
  -- The anti-quotation matches both `equations` and `eqns`.
  | `(Parser.Command.printEqns| #print%$printTk equations%$eqnsTk $id:ident) => do
    let printTk ← fmt printTk
    let eqnsTk ← fmt eqnsTk
    let keywords := Layouts.spacedAtomic #[printTk, eqnsTk]
    let id ← fmt id
    return Layouts.pseudoApplication #[keywords, id]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.printTacTags]
public def fmtPrintTacTags : Fmt := fun
  | `(Parser.Command.printTacTags| #print%$printTk tactic%$tacticTk tags%$tagsTk) => do
    let printTk ← fmt printTk
    let tacticTk ← fmt tacticTk
    let tagsTk ← fmt tagsTk
    let keywords := Layouts.spacedAtomic #[printTk, tacticTk, tagsTk]
    return keywords
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.withExporting]
public def fmtWithExporting : Fmt := fun
  | `(Parser.Command.withExporting| #with_exporting%$withExportingTk $cmd:command) => do
    let withExportingTk ← fmt withExportingTk
    let cmd ← fmt cmd
    return Layouts.lines #[withExportingTk, cmd]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.withWeakNamespace]
public def fmtWithWeakNamespace : Fmt := fun
  | `(Parser.Command.withWeakNamespace| with_weak_namespace%$withWeakNamespaceTk $id:ident $cmd:command) =>
    do
      let withWeakNamespaceTk ← fmt withWeakNamespaceTk
      let id ← fmt id
      let app := Layouts.pseudoApplication #[withWeakNamespaceTk, id]
      let cmd ← fmt cmd
      return combine #[.withSepAfter app ⟨hardNl, nested⟩, cmd]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.deprecatedSyntax]
public def fmtDeprecatedSyntax : Fmt := fun
  | `(Parser.Command.deprecatedSyntax|
      deprecated_syntax%$deprecatedSyntaxTk $id:ident $[$msg?:str]?
        $[ (%$lbTk? since%$sinceTk? :=%$colonEqTk? $since?:str )%$rbTk?]?) => do
    let deprecatedSyntaxTk ← fmt deprecatedSyntaxTk
    let id ← fmt id
    let msg? ← fmt? msg?
    let sinceParam? ← fmtNamedArgumentTerm? lbTk? sinceTk? colonEqTk? since? rbTk?
    return Layouts.pseudoApplication #[deprecatedSyntaxTk, id, msg?, sinceParam?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.deprecated_module]
public def fmtDeprecatedModule : Fmt := fun
  | `(Parser.Command.deprecated_module|
      deprecated_module%$deprecatedModuleTk $[$msg?:str]?
        $[ (%$lbTk? since%$sinceTk? :=%$colonEqTk? $since?:str )%$rbTk?]?) => do
    let deprecatedModuleTk ← fmt deprecatedModuleTk
    let msg? ← fmt? msg?
    let sinceParam? ← fmtNamedArgumentTerm? lbTk? sinceTk? colonEqTk? since? rbTk?
    return Layouts.pseudoApplication #[deprecatedModuleTk, msg?, sinceParam?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.docs_to_verso]
public def fmtDocsToVerso : Fmt := fun
  | `(Parser.Command.docs_to_verso| docs_to_verso%$docsToVersoTk $ids:ident,*) => do
    let docsToVersoTk ← fmt docsToVersoTk
    let ids ← fmtTSepArray ids
    return Layouts.keywordPrefixedSepFill docsToVersoTk ids .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.register_tactic_tag]
public def fmtRegisterTacticTag : Fmt := fun
  | `(Parser.Command.register_tactic_tag|
      $[$docComment?:docComment]? register_tactic_tag%$registerTacticTagTk $id:ident $name:str) =>
    do
      let docComment? ← fmt? docComment?
      let registerTacticTagTk ← fmt registerTacticTagTk
      let id ← fmt id
      let name ← fmt name
      let cmd := Layouts.pseudoApplication #[registerTacticTagTk, id, name]
      return Layouts.lines #[docComment?, cmd]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.tactic_extension]
public def fmtTacticExtension : Fmt := fun
  | `(Parser.Command.tactic_extension|
      $[$docComment?:docComment]? tactic_extension%$tacticExtensionTk $id:ident) => do
    let docComment? ← fmt? docComment?
    let tacticExtensionTk ← fmt tacticExtensionTk
    let id ← fmt id
    let cmd := Layouts.pseudoApplication #[tacticExtensionTk, id]
    return Layouts.lines #[docComment?, cmd]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.registerErrorExplanationStx]
public def fmtRegisterErrorExplanationStx : Fmt := fun
  | `(Parser.Command.registerErrorExplanationStx|
      $[$docComment?:docComment]? register_error_explanation%$registerErrorExplanationTk $id:ident $t:term) =>
    do
      let docComment? ← fmt? docComment?
      let registerErrorExplanationTk ← fmt registerErrorExplanationTk
      let id ← fmt id
      let t ← fmt t
      let cmd := Layouts.pseudoApplication #[registerErrorExplanationTk, id, t]
      return Layouts.lines #[docComment?, cmd]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.recommended_spelling]
public def fmtRecommendedSpelling : Fmt := fun
  | `(Parser.Command.recommended_spelling|
      $[$docComment?:docComment]?
      recommended_spelling%$recommendedSpellingTk $spelling:str for%$forTk $notationStr:str in%$inTk
        [%$lbTk $ids:ident,* ]%$rbTk) => do
    let docComment? ← fmt? docComment?
    let recommendedSpellingTk ← fmt recommendedSpellingTk
    let spelling ← fmt spelling
    let lhs := Layouts.pseudoApplication #[recommendedSpellingTk, spelling]
    let forTk ← fmt forTk
    let notationStr ← fmt notationStr
    let inTk ← fmt inTk
    let lbTk ← fmt lbTk
    let ids ← fmtTSepArray ids
    let rbTk ← fmt rbTk
    let forNotation := Layouts.keywordPrefixedTerm forTk notationStr
    let «in» := Layouts.keywordPrefixedCollection inTk lbTk ids rbTk
    let cmd := Layouts.blocks #[lhs, forNotation, «in»]
    return Layouts.lines #[docComment?, cmd]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.initializeKeyword]
public def fmtInitializeKeyword : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.initialize]
public def fmtInitialize : Fmt := fun
  | `(Parser.Command.initialize|
      $declModifiers:declModifiers $kw:initializeKeyword $[$id?:ident :%$colonTk? $type?:term ←%$leftArrowTk?]?
        $doSeq:doSeq) => do
    let kw ← fmt kw
    let id? ← fmt? id?
    let colonTk? ← fmt? colonTk?
    let type? ← fmt? type?
    let leftArrowTk? ← fmt? leftArrowTk?
    let doSeq ← fmt doSeq
    if leftArrowTk?.isAlwaysEmpty then
      let decl := Layouts.keywordPrefixedSeq kw doSeq .nonSticky
      fmtDeclWithDeclModifiers declModifiers decl
    else
      let signature := Layouts.globalSignature #[kw, id?] #[] colonTk? type?
      let decl := Layouts.assignmentDeclaration signature leftArrowTk? doSeq
      fmtDeclWithDeclModifiers declModifiers decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.mutual]
public def fmtMutual : Fmt := fun
  | `(Parser.Command.mutual| mutual%$mutualTk $[$cmds:command]* end%$endTk) => do
    let elems := #[mutualTk] ++ cmds ++ #[endTk]
    fmtArrayWithRetainedIntermediateNewlinesAndComments elems
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.quot]
public def fmtCommandQuot : Fmt := fmtAtomic
