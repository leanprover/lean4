/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.FmtM.CommonFormatters
meta import Lean.Parser.Term.Basic
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Term.hole]
public def fmtHole : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.syntheticHole]
public def fmtSyntheticHole : Fmt := fun
  | `(Parser.Term.syntheticHole| ?%$questionTk $id:ident) => do
    let questionTk ← fmt questionTk
    let id ← fmt id
    return Layouts.atomic #[questionTk, id]
  | `(Parser.Term.syntheticHole| ?%$questionTk _%$holeTk) => do
    let questionTk ← fmt questionTk
    let holeTk ← fmt holeTk
    return Layouts.atomic #[questionTk, holeTk]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.omission]
public def fmtOmission : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.explicitBinder]
public def fmtExplicitBinder : Fmt := fun
  | `(explicitBinderF| (%$lbTk $ids* $[:%$typeAscriptionTk? $type?:term]? $[$tacticOrDefault?]? )%$rbTk) =>
    fmtBinder #[lbTk] ids #[] typeAscriptionTk? type? tacticOrDefault? #[rbTk]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.implicitBinder]
public def fmtImplicitBinder : Fmt := fun
  | `(implicitBinderF| {%$lbTk $ids* $[:%$typeAscriptionTk? $type?:term]? }%$rbTk) =>
    fmtBinder #[lbTk] ids #[] typeAscriptionTk? type? none #[rbTk]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.strictImplicitBinder]
public def fmtStrictImplicitBinder : Fmt := fun
  | `(strictImplicitBinderF| {%$lbTk1 {%$lbTk2 $ids* $[:%$typeAscriptionTk? $type?:term]? }%$rbTk1 }%$rbTk2) =>
    fmtBinder #[lbTk1, lbTk2] ids #[] typeAscriptionTk? type? none #[rbTk1, rbTk2] (kind := .global)
  | `(strictImplicitBinderF| {%$lbTk1 {%$lbTk2 $ids* $[:%$typeAscriptionTk? $type?:term]? ⦄%$rbTk) =>
    fmtBinder #[lbTk1, lbTk2] ids #[] typeAscriptionTk? type? none #[rbTk] (kind := .global)
  | `(strictImplicitBinderF| ⦃%$lbTk $ids* $[:%$typeAscriptionTk? $type?:term]? }%$rbTk1 }%$rbTk2) =>
    fmtBinder #[lbTk] ids #[] typeAscriptionTk? type? none #[rbTk1, rbTk2] (kind := .global)
  | `(strictImplicitBinderF| ⦃%$lbTk $ids* $[:%$typeAscriptionTk? $type?:term]? ⦄%$rbTk) =>
    fmtBinder #[lbTk] ids #[] typeAscriptionTk? type? none #[rbTk] (kind := .global)
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.instBinder]
public def fmtInstBinder : Fmt := fun
  | `(Parser.Term.instBinder| [%$lbTk $[$id?:ident :%$typeAscriptionTk?]? $classType:term ]%$rbTk) =>
    fmtBinder #[lbTk] id?.toArray #[] typeAscriptionTk? classType none #[rbTk]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.structInstArrayRef]
public def fmtStructInstArrayRef : Fmt := fun
  | `(Parser.Term.structInstArrayRef| [%$lbTk $idx:term ]%$rbTk) => do
    let lbTk ← fmt lbTk
    let idx ← fmt idx
    let rbTk ← fmt rbTk
    return Layouts.bracketed lbTk idx rbTk <| .sparse «break» (stickynessKind := .coequal)
  | _ =>
    throw .partialFormatter

@[expose] public def structInstLValKinds := [`ident, `fieldIdx, ``Parser.Term.structInstArrayRef]

public structure StructInstLValElem where
  dotTk? : Option Syntax
  elem : Syntax

public def splitStructInstLValIdent (id : TSyntax `ident) : Array StructInstLValElem := Id.run do
  -- The Lean parser parses LVals that consist purely of dots as identifiers, and the elaborator
  -- then splits these identifiers into fields.
  -- Since LVals can in principle become quite complex (e.g. with array references),
  -- we split these identifiers into their components so that we can still format them
  -- as separate components.
  -- In some cases, splitting an identifier into its components is not possible, e.g. when the
  -- identifier contains macro scopes, in which case we fall back to not attempting to split it.
  let some (comps, seps) := Syntax.identComponents? id
    | return #[⟨none, id⟩]
  let comps := comps.toArray
  let seps := seps.toArray
  -- comps.size - 1 = seps.size
  let mut r := #[⟨none, comps[0]!⟩]
  for i in (1...comps.size) do
    r := r.push ⟨seps[i - 1]!, comps[i]!⟩
  return r

public def splitStructInstLValRhs (rhs : Syntax) : FmtM (Array StructInstLValElem) := do
  rhs.getArgs.flatMapM fun rhsElem => do
    let kind := rhsElem.getKind
    if kind == groupKind then
      let dotTk ← getStxArg! rhsElem 0
      let elem ← getStxArg! rhsElem 1
      let elemKind := elem.getKind
      if elemKind == `ident then
        return splitStructInstLValIdent ⟨elem⟩ |>.modify 0 ({ · with dotTk? := dotTk })
      else if elemKind == `fieldIdx then
        return #[⟨dotTk, elem⟩]
      else
        throw .partialFormatter
    else if kind == ``Parser.Term.structInstArrayRef then
      return #[⟨none, rhsElem⟩]
    else
      throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.structInstLVal]
public def fmtStructInstLVal : Fmt := fun stx => do
  let lhs ← getStxArg! stx 0
  if ! structInstLValKinds.contains lhs.getKind then
    throw .partialFormatter
  let lhs : TSyntax structInstLValKinds := ⟨lhs⟩
  let lhsElems : Array StructInstLValElem :=
    if let `($id:ident) := lhs then
      splitStructInstLValIdent id
    else
      #[⟨none, lhs⟩]
  let rhs ← getStxArg! stx 1
  let rhsElems ← splitStructInstLValRhs rhs
  let elems := lhsElems ++ rhsElems
  let elemComponents : Array TaggedDoc.Component ←
    elems.flatMapM fun e => do
      let dotTk? ← fmt? e.dotTk?
      let elem ← fmt e.elem
      return #[.withSepBefore dotTk? «break», elem]
  return nested <| maybeFlattened <| combine elemComponents

public def convertStructInstFieldBinders
    (binders : TSyntaxArray ``Parser.Term.structInstFieldBinder)
    : TSyntaxArray binderKinds :=
  binders.map fun
    | `(Parser.Term.structInstFieldBinder| $id:ident) => id
    | `(Parser.Term.structInstFieldBinder| $hole:hole) => hole
    | `(Parser.Term.structInstFieldBinder| $bracketedBinder:bracketedBinder) => bracketedBinder

public structure StructInstFieldDecl where
  format (signature : TaggedDoc) : TaggedDoc
deriving Inhabited, TypeName

public def mkStructInstFieldDecl (format : (signature : TaggedDoc) → TaggedDoc) : TaggedDoc :=
  failure.addMetaData (StructInstFieldDecl.mk format) fun v f => {
    v with
    format signature := propagateMetaData (v.format signature) f
  }

public def getStructInstFieldDecl? (doc : TaggedDoc) : Option StructInstFieldDecl :=
  doc.getMetaData? StructInstFieldDecl

@[builtin_fmt Lean.Parser.Term.structInstField]
public def fmtStructInstField : Fmt := fun
  | `(Parser.Term.structInstField|
      $lval:structInstLVal $[$binders?:structInstFieldBinder* $[:%$typeAscriptionTk? $type?:term]?
        $structInstFieldDecl?:structInstFieldDecl]?) => do
    let binders := convertStructInstFieldBinders <| binders?.getD #[]
    let typeAscriptionTk? := typeAscriptionTk?.join
    let type? := type?.join
    let signature ← fmtLocalSignature lval binders typeAscriptionTk? type?
    -- Since `structInstFieldDecl` is a parser category and the kind of separation from the
    -- signature depends on the specific kind of `structInstFieldDecl`,
    -- `structInstFieldDecl` (unusually) manages its own leading whitespace.
    let structInstFieldDecl? ← fmt? structInstFieldDecl?
    if structInstFieldDecl?.isAlwaysEmpty then
      return signature
    let some structInstFieldDecl := getStructInstFieldDecl? structInstFieldDecl?
      | throw .partialFormatter
    return structInstFieldDecl.format signature
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticSeq1Indented]
public def fmtTacticSeq1Indented : Fmt := fun
  | `(Parser.Tactic.tacticSeq1Indented| $tactics:tactic;*) => do fmtSeq tactics none
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticSeqBracketed]
public def fmtTacticSeqBracketed : Fmt := fun
  | `(Parser.Tactic.tacticSeqBracketed|
      {%$lbTk
        $tactics:tactic;*
      }%$rbTk ) => do
    let lbTk ← fmt lbTk
    let tactics ← fmtSeq tactics none
    let rbTk ← fmt rbTk
    return Layouts.bracketed lbTk tactics rbTk <| .sparse hardNl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticSeq]
public def fmtTacticSeq : Fmt := fun
  | `(Parser.Tactic.tacticSeq| $tacticSeq:tacticSeq1Indented) => fmt tacticSeq
  | `(Parser.Tactic.tacticSeq| $tacticSeq:tacticSeqBracketed) => fmt tacticSeq
  | _ => throw .partialFormatter
