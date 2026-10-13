/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PrettyPrinter

namespace Lean.Compiler.LCNF

public inductive Uniqueness where
  | unique
  | top
  deriving Inhabited, BEq, Repr

def Uniqueness.join : Uniqueness → Uniqueness → Uniqueness
  | .unique, .unique =>  .unique
  | _, _ => .top

private abbrev decLt (a b : Name × Uniqueness) : Bool :=
  Name.quickLt a.fst b.fst

private abbrev findAtSorted? (entries : Array (Name × Uniqueness)) (fid : Name) :
    Option Uniqueness :=
  entries.binSearch (fid, default) decLt |>.map Prod.snd

builtin_initialize uniquenessExt :
    SimplePersistentEnvExtension (Name × Uniqueness) (PHashMap Name Uniqueness) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => {}
    addEntryFn := fun s ⟨e, n⟩ => s.insert e n
    exportEntriesFnEx? := some fun _ s _ =>
      -- preserved for non-modules, make non-persistent at some point?
      { exported := #[], server := #[], «private» := s.toArray.qsort decLt }
    asyncMode := .sync  -- compilation is non-parallel anyway
    replay? := some <| SimplePersistentEnvExtension.replayOfFilter (!·.contains ·.1) (fun s ⟨e, n⟩ => s.insert e n)
  }

def addFunctionSummaryExt (env : Environment) (fid : Name) (u : Uniqueness) : Environment :=
  uniquenessExt.addEntry env (fid, u)

def getFunctionSummaryExt (env : Environment) (fid : Name) : Option Uniqueness :=
  findExtEntry? env uniquenessExt fid findAtSorted? (·.2.find?)

structure State where
  variables : Std.HashMap FVarId Uniqueness := {}
  summaries : Std.HashMap Name Uniqueness := {}
  modified : Bool := false

structure Context where
  currFn : Name

abbrev InferM := ReaderT Context StateRefT State CompilerM

public structure UniquenessAnalysisResult where
  variables : Std.HashMap FVarId Uniqueness
  summaries : Std.HashMap Name Uniqueness

@[inline]
def joinVar (fvarId : FVarId) (v : Uniqueness) : InferM Unit := do
  modify fun s =>
    let old := s.variables.getD fvarId .unique
    let new := old.join v
    if old == new then
      { s with variables := s.variables.insert fvarId new }
    else
      { s with variables := s.variables.insert fvarId new, modified := true }

def getVarUniqueness (fvarId : FVarId) : InferM Uniqueness := do
  return (← get).variables.getD fvarId .unique

def joinCurrSummary (v : Uniqueness) : InferM Unit := do
  let currFn := (← read).currFn
  modify fun s =>
    let old := s.summaries.getD currFn .unique
    let new := old.join v
    if old == new then
      s
    else
      { s with summaries := s.summaries.insert currFn new, modified := true }

def getSummary (name : Name) : InferM Uniqueness := do
  match getFunctionSummaryExt (← getEnv) name with
  | some s => return s
  | none => return (← get).summaries.getD name .top

partial def Code.infer (code : Code .impure) : InferM Unit := do
  match code with
  | .jp decl k =>
    for p in decl.params do
      unless (← get).variables.contains p.fvarId do
        modify fun s => { s with variables := s.variables.insert p.fvarId .unique }
    k.infer
    decl.value.infer
  | .let decl k =>
    inferLetValue decl.fvarId decl.value
    k.infer
  | .jmp jpId args =>
    let some decl ← findFunDecl? (pu := .impure) jpId | unreachable!
    for arg in args, p in decl.params do
      if let .fvar arg := arg then
        let argValue ← getVarUniqueness arg
        joinVar p.fvarId argValue
  | .uset (k := k) .. | .sset (k := k) .. | .del (k := k) .. | .setTag (k := k) .. => k.infer
  | .inc (fvarId := fvarId) (k := k) .. | .dec (fvarId := fvarId) (k := k) .. =>
    joinVar fvarId .top
    k.infer
  | .cases cs => cs.alts.forM (·.forCodeM Code.infer)
  | .return fvarId => joinCurrSummary (← getVarUniqueness fvarId)
  | .unreach .. => return ()
  | .oset .. => unreachable!
where
  inferLetValue (z : FVarId) (v : LetValue .impure) : InferM Unit := do
    match v with
    | .fap f args =>
      args.forM fun arg => do
        let .fvar fvarId := arg | return ()
        joinVar fvarId .top
      let value ← getSummary f
      joinVar z value
    | .ctor _ args | .pap _ args | .reuse _ _ _ args =>
      args.forM fun arg => do
        let .fvar fvarId := arg | return ()
        joinVar fvarId .top
      joinVar z .unique
    | .sproj .. | .uproj .. | .box .. | .erased | .unbox .. | .reset .. => joinVar z .unique
    | .lit v =>
      match v with
      | .str .. => joinVar z .top
      | .uint8 .. | .uint16 .. | .uint32 .. | .uint64 .. | .usize .. => joinVar z .unique
      | .nat .. => joinVar z .top -- TODO
    | .fvar fvarId args =>
      joinVar fvarId .top
      args.forM fun arg => do
        let .fvar fvarId := arg | return ()
        joinVar fvarId .top
      joinVar z .top
    | .oproj .. => joinVar z .top
    | .isShared .. => unreachable!

def Decl.infer (decl : Decl .impure) : InferM Unit := do
  withReader (fun ctx => { ctx with currFn := decl.name }) do
    if !decl.safe || decl.params.isEmpty then
      joinCurrSummary .top
      return ()

    decl.params.forM fun p => joinVar p.fvarId .top
    match decl.value with
    | .code code .. =>
      withTraceNode `Compiler.uniqueness (fun _ => return m!"Analyzing {decl.name}") do
        code.infer
    | .extern .. => joinCurrSummary .top

    trace[Compiler.uniqueness] m!"{decl.name} summary: {repr (← getSummary decl.name)}"

public partial def inferSccUniqueness (decls : Array (Decl .impure)) :
    CompilerM UniquenessAnalysisResult := do
  let (_, res) ← loop 0
    |>.run { currFn := .anonymous }
    |>.run {
      summaries := Std.HashMap.ofArray (decls.map (fun decl => (decl.name, if decl.safe then .unique else .top)))
    }
  for decl in decls do
    let summary := res.summaries[decl.name]!
    modifyEnv fun e => addFunctionSummaryExt e decl.name summary
  return {
    variables := res.variables
    summaries := res.summaries
  }
where
  loop (n : Nat) : InferM Unit := do
    modify fun s => { s with modified := false }
    step
    if (← get).modified then
      loop (n + 1)
    else
      trace[Compiler.uniqueness] m!"Termination after {n} steps"
      return ()

  step : InferM Unit := do
    for decl in decls do
      decl.infer

builtin_initialize
  registerTraceClass `Compiler.uniqueness (inherited := true)

end Lean.Compiler.LCNF
