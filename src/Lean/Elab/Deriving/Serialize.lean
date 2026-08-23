/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Elab.Deriving.Basic
public import Lean.Elab.Deriving.Util
import Std.Internal.Derse.Se.Basic

public section

namespace Lean.Elab.Deriving.Serialize
open Lean.Elab.Command
open Lean.Parser.Term
open Lean.Meta
open Std.Internal.Derse

/--
Returns `[Serialize α]` binders for the type parameters of `indVal`. `mkInstImplicitBinders`
cannot be used here: `Serialize` is universe polymorphic over the serializer monad, so `Serialize α`
leaves universe metavariables behind that make its `mkAppM`-based type correctness check throw.
-/
def mkSerializeInstBinders (indVal : InductiveVal) (argNames : Array Name) :
    TermElabM (Array Syntax) :=
  forallBoundedTelescope indVal.type indVal.numParams fun xs _ => do
    let mut binders := #[]
    for h : i in *...xs.size do
      if (← whnfD (← inferType xs[i])).isSort then
        let className := mkCIdent ``Std.Internal.Derse.Serialize
        binders := binders.push (← `(instBinderF| [$className:ident $(mkIdent argNames[i]!):ident]))
    return binders

open TSyntax.Compat in
/--
Builds the header of a serialization function: the binders from `mkHeader` followed by the
serializer binders that `Serialize.serialize` abstracts over and the value that is serialized.
Returns the header together with the identifiers for the serializer monad and its result type,
which form the return type of the function.
-/
def mkSerializeHeader (indVal : InductiveVal) : TermElabM (Header × Ident × Ident) := do
  let header ← mkHeader ``Std.Internal.Derse.Serialize 0 indVal
  let header := { header with
    binders := header.binders ++ (← mkSerializeInstBinders indVal header.argNames) }
  let σ := mkIdent (← mkFreshUserName `σ)
  let m := mkIdent (← mkFreshUserName `m)
  let ρ := mkIdent (← mkFreshUserName `ρ)
  let ε := mkIdent (← mkFreshUserName `ε)
  let targetName ← mkFreshUserName `x
  let binders := header.binders
    ++ #[← `(implicitBinderF| {$σ:ident : Type _}),
         ← `(implicitBinderF| {$m:ident : Type _ → Type _}),
         ← `(implicitBinderF| {$ρ:ident : Type _}),
         ← `(implicitBinderF| {$ε:ident : Type _}),
         ← `(instBinderF| [Monad $m:ident]),
         ← `(instBinderF| [MonadStateOf $σ:ident $m:ident]),
         ← `(instBinderF| [MonadExceptOf $ε:ident $m:ident]),
         ← `(instBinderF| [Serializer $σ:ident $m:ident $ρ:ident $ε:ident]),
         ← `(explicitBinderF| ($(mkIdent targetName):ident : $(header.targetType)))]
  return ({ header with binders := binders, targetNames := #[targetName] }, m, ρ)

def mkSerializeBodyForStruct (header : Header) (indName : Name) : TermElabM Term := do
  let typeStr := quote indName.eraseMacroScopes.getString!
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  if fields.isEmpty then
    return ← ``(Serializer.serializeUnitStructure $typeStr)
  let target := mkIdent header.targetNames[0]!
  let state := mkIdent (← mkFreshUserName `state)
  let first ← ``(Serializer.serializeStructBegin $typeStr $(quote fields.size))
  let mut items := #[← `(doSeqItem| let $state:ident ← $first:term)]
  for i in *...fields.size do
    let field := fields[i]!
    let fieldName := field.eraseMacroScopes.getString!
    -- `?`-suffixed `Option` fields follow the `ToJson` convention: the suffix is dropped from the
    -- serialized name and the field is omitted entirely when `none`.
    let trimmed := fieldName.dropEndWhile (· == '?') |>.copy
    let fieldStr := quote trimmed
    let step ←
      if trimmed == fieldName then
        ``(Serializer.serializeStructField $state $(quote i) $fieldStr ($target).$(mkIdent field))
      else
        `(match ($target).$(mkIdent field) with | none => pure $state | some val => Serializer.serializeStructField $state $(quote i) $fieldStr val)
    items := items.push (← `(doSeqItem| let $state:ident ← $step:term))
  items := items.push (← `(doSeqItem| Serializer.serializeStructEnd $state))
  `(do $items:doSeqItem*)

def mkSerializeBodyForInduct (header : Header) (indName : Name) : TermElabM Term := do
  let indVal ← getConstInfoInduct indName
  let typeStr := quote indName.eraseMacroScopes.getString!
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts indVal fun ctor args userNames => do
    let ctorStr := quote ctor.name.eraseMacroScopes.getString!
    let altIdx := quote ctor.cidx
    if args.isEmpty then
      ``(Serializer.serializeUnitAlt $typeStr $altIdx $ctorStr)
    else if args.size == 1 && userNames.isNone then
      let (x, _) := args[0]!
      ``(Serializer.serializeNewtypeAlt $typeStr $altIdx $ctorStr $x:ident)
    else
      let state := mkIdent (← mkFreshUserName `state)
      let mut items := #[]
      match userNames with
      | some userNames =>
        let first ← ``(Serializer.serializeNamedAltBegin $typeStr $altIdx $ctorStr $(quote args.size))
        items := items.push (← `(doSeqItem| let $state:ident ← $first:term))
        for i in *...args.size do
          let (x, _) := args[i]!
          let fieldStr := quote userNames[i]!.eraseMacroScopes.getString!
          let step ← ``(Serializer.serializeNamedAltField $state $(quote i) $fieldStr $x:ident)
          items := items.push (← `(doSeqItem| let $state:ident ← $step:term))
        items := items.push (← `(doSeqItem| Serializer.serializeNamedAltEnd $state))
      | none =>
        let first ← ``(Serializer.serializeAnonAltBegin $typeStr $altIdx $ctorStr $(quote args.size))
        items := items.push (← `(doSeqItem| let $state:ident ← $first:term))
        for i in *...args.size do
          let (x, _) := args[i]!
          let step ← ``(Serializer.serializeAnonAltField $state $(quote i) $x:ident)
          items := items.push (← `(doSeqItem| let $state:ident ← $step:term))
        items := items.push (← `(doSeqItem| Serializer.serializeAnonAltEnd $state))
      `(do $items:doSeqItem*)
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkAlts
    (indVal : InductiveVal)
    (rhs : ConstructorVal → Array (Ident × Expr) → Option (Array Name) → TermElabM Term) :
      TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let alt ← forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut patterns := #[]
        -- add `_` pattern for indices
        for _ in *...indVal.numIndices do
          patterns := patterns.push (← `(_))
        let mut ctorArgs := #[]
        -- add `_` for inductive parameters, they are inaccessible
        for _ in *...indVal.numParams do
          ctorArgs := ctorArgs.push (← `(_))
        -- bound constructor arguments and their types
        let mut binders := #[]
        let mut userNames := #[]
        for i in *...ctorInfo.numFields do
          let x := xs[indVal.numParams + i]!
          let localDecl ← x.fvarId!.getDecl
          if !localDecl.userName.hasMacroScopes then
            userNames := userNames.push localDecl.userName
          let a := mkIdent (← mkFreshUserName `a)
          binders := binders.push (a, localDecl.type)
          ctorArgs := ctorArgs.push a
        patterns := patterns.push (← `(@$(mkIdent ctorInfo.name):ident $ctorArgs:term*))
        let rhs ← rhs ctorInfo binders
          (if userNames.size == binders.size then some userNames else none)
        `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
      alts := alts.push alt
    return alts

def mkSerializeBody (header : Header) (indName : Name) : TermElabM Term := do
  if isStructure (← getEnv) indName then
    mkSerializeBodyForStruct header indName
  else
    mkSerializeBodyForInduct header indName

def mkSerializeAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal := ctx.typeInfos[i]!
  let (header, m, ρ) ← mkSerializeHeader indVal
  let binders := header.binders
  let mut body ← mkSerializeBody header indVal.name
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx ``Std.Internal.Derse.Serialize header.argNames
    body ← mkLet letDecls body
    `(partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $m $ρ := $body:term)
  else
    `(def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $m $ρ := $body:term)

def mkSerializeMutualBlock (ctx : Context) : TermElabM Command := do
  let mut auxDefs := #[]
  for i in *...ctx.typeInfos.size do
    auxDefs := auxDefs.push (← mkSerializeAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

open TSyntax.Compat in
/-- Like `mkInstanceCmds`, but with the instance binders from `mkSerializeInstBinders`. -/
def mkSerializeInstanceCmds (ctx : Context) (typeNames : Array Name) :
    TermElabM (Array Command) := do
  let mut instances := #[]
  for i in *...ctx.typeInfos.size do
    let indVal := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName := ctx.auxFunNames[i]!
      let argNames ← mkInductArgNames indVal
      let binders ← mkImplicitBinders argNames
      let binders := binders ++ (← mkSerializeInstBinders indVal argNames)
      let indType ← mkInductiveApp indVal argNames
      let type ← `($(mkCIdent ``Std.Internal.Derse.Serialize) $indType)
      let val ← `(⟨$(mkIdent auxFunName)⟩)
      let instCmd ← `(instance $(mkIdent ctx.instName):ident $binders:implicitBinder* : $type := $val:term)
      instances := instances.push instCmd
  return instances

private def mkSerializeInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext ``Std.Internal.Derse.Serialize "serialize" declName (supportsRec := false)
  let cmds := #[← mkSerializeMutualBlock ctx] ++ (← mkSerializeInstanceCmds ctx #[declName])
  trace[Elab.Deriving.serialize] "\n{cmds}"
  return cmds

def mkSerializeInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkSerializeInstance declName
      cmds.forM elabCommand
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler ``Std.Internal.Derse.Serialize mkSerializeInstanceHandler

  registerTraceClass `Elab.Deriving.serialize

end Lean.Elab.Deriving.Serialize
