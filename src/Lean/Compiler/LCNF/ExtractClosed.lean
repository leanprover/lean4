/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Zwarich
-/
module

prelude
public import Lean.Compiler.ClosedTermCache
public import Lean.Compiler.NeverExtractAttr
public import Lean.Compiler.LCNF.Internalize
public import Lean.Compiler.LCNF.ToExpr
import Lean.Compiler.LCNF.ElimDead
import Lean.Compiler.LCNF.DependsOn
meta import Init.Data.FloatArray.Basic
import Lean.Compiler.LCNF.ElimDead

public section

namespace Lean.Compiler.LCNF
namespace ExtractClosed

abbrev ExtractM := StateRefT (Array (CodeDecl .pure)) CompilerM

mutual

partial def extractLetValue (v : LetValue .pure) : ExtractM Unit := do
  match v with
  | .const _ _ args => args.forM extractArg
  | .fvar fnVar args =>
    extractFVar fnVar
    args.forM extractArg
  | .proj _ _ baseVar => extractFVar baseVar
  | .lit _ | .erased => return ()

partial def extractArg (arg : Arg .pure) : ExtractM Unit := do
  match arg with
  | .fvar fvarId => extractFVar fvarId
  | .type _ | .erased => return ()

partial def extractFVar (fvarId : FVarId) : ExtractM Unit := do
  if let some letDecl ← findLetDecl? fvarId then
    modify fun decls => decls.push (.let letDecl)
    extractLetValue letDecl.value

end

def isIrrelevantArg (arg : Arg .pure) : Bool :=
  match arg with
  | .erased | .type _ => true
  | .fvar _ => false

structure Context where
  baseName : Name
  sccDecls : Array (Decl .pure)

structure State where
  decls : Array (Decl .pure) := {}
  /--
  Cache for `shouldExtractFVar` in order to avoid superlinear behavior.
  -/
  fvarDecisionCache : Std.HashMap FVarId Bool := {}

abbrev M := ReaderT Context $ StateRefT State CompilerM

mutual

partial def shouldExtractLetValue (isRoot : Bool) (v : LetValue .pure) : M Bool := do
  match v with
  | .lit (.str _) => return true
  | .lit (.nat v) =>
    -- The old compiler's implementation used the runtime's `is_scalar` function, which
    -- introduces a dependency on the architecture used by the compiler.
    return !isRoot || v >= Nat.pow 2 63
  | .lit _ | .erased => return !isRoot
  | .const name _ args =>
    if (← read).sccDecls.any (·.name == name) then
      return false
    if hasNeverExtractAttribute (← getEnv) name then
      return false
    if isRoot then
      if let some constInfo := (← getEnv).find? name then
        let shouldExtract := match constInfo with
        | .defnInfo val => val.type.isForall
        | .ctorInfo _ => !(args.all isIrrelevantArg)
        | _ => true
        if !shouldExtract then
          return false
      if let some decl ← LCNF.getMonoDecl? name then
        -- We don't want to extract constants as root terms
        if decl.getArity == 0 then
          return false
    args.allM shouldExtractArg
  | .fvar fnVar args => return (← shouldExtractFVar fnVar) && (← args.allM shouldExtractArg)
  | .proj _ _ baseVar => shouldExtractFVar baseVar

partial def shouldExtractArg (arg : Arg .pure) : M Bool := do
  match arg with
  | .fvar fvarId => shouldExtractFVar fvarId
  | .type _ | .erased => return true

partial def shouldExtractFVar (fvarId : FVarId) : M Bool := do
  if let some result := (← get).fvarDecisionCache[fvarId]? then
    return result
  else
    let result ← go
    modify fun s => { s with fvarDecisionCache := s.fvarDecisionCache.insert fvarId result }
    return result
where
  go : M Bool := do
    if let some letDecl ← findLetDecl? fvarId then
      shouldExtractLetValue false letDecl.value
    else
      return false

end

/--
Check if `let decl; k` forms an `Array`, `ByteArray`, or `FloatArray` literal. They consist of some
initial allocation (`Array.mkEmpty` or `Array.emptyWithCapacity`) followed by a sequence of
`Array.push` and for the scalar variants finally `ByteArray.mk` or `FloatArray.mk`.

We identify these literals by matching this pattern and ensuring that only the last `push`/`mk` from
the sequence is used in the final continuation. If that is the case, we can pull out the entire
literal as one closed declaration. This avoids the quadratic overhead of repeated `Array.push` calls
on persistent `Array` objects during initialization.
-/
def searchArrayLiteral (decl : LetDecl .pure) (k : Code .pure) :
    M (Option (LetDecl .pure × Code .pure)) := do
  let .const ``Array.push  _ #[_, .fvar parentId, _] := decl.value | return none
  let some parentDecl ← findLetDecl? (pu := .pure) parentId | return none
  match parentDecl.value with
  | .const ``Array.mkEmpty _ #[_, .fvar sizeFVar]
  | .const ``Array.emptyWithCapacity _ #[_, .fvar sizeFVar] =>
    let some (.lit (.nat size)) ← findLetValue? (pu := .pure) sizeFVar | return none
    identifyChain parentDecl.fvarId decl k {} size
  | _ => return none
where
  identifyChain (prevArrayId : FVarId) (decl : LetDecl .pure) (k : Code .pure)
      (illegalSet : FVarIdSet) (size : Nat) : M (Option (LetDecl .pure × Code .pure)) := do
    match size with
    | 0 => return none
    | nextSize + 1 =>
      let .const ``Array.push _ #[_, .fvar arrId, elemArg] := decl.value | return none
      if arrId != prevArrayId then return none
      if !(← shouldExtractArg elemArg) then return none
      if nextSize != 0 then
        let illegalSet := illegalSet.insert decl.fvarId
        let .let nextDecl nextK := k | return none
        identifyChain decl.fvarId nextDecl nextK illegalSet nextSize
      else
        let occursCheck (decl : LetDecl .pure) (k : Code .pure) (illegalSet : FVarIdSet) := do
          if k.dependsOn illegalSet then return none
          return some (decl, k)
        -- At this point we can be at the end of an `Array` literal or right before the end of a
        -- `ByteArray` or `FloatArray` literal, let's check.
        match k with
        | .let nextDecl@{ value := .const ``ByteArray.mk _ #[.fvar arrayId] _, .. } nextK
        | .let nextDecl@{ value := .const ``FloatArray.mk _ #[.fvar arrayId] _, .. } nextK =>
          if arrayId != decl.fvarId then
            occursCheck decl k illegalSet
          else
            let illegalSet := illegalSet.insert decl.fvarId
            occursCheck nextDecl nextK illegalSet
        | _ => occursCheck decl k illegalSet

mutual

partial def visitCode (code : Code .pure) : M (Code .pure) := do
  match code with
  | .let decl k =>
    let visitLetDefault := do
      if let some (decl, k) ← searchArrayLiteral decl k then
        let name ← performExtraction decl
        let decl ← decl.updateValue (.const name [] #[])
        return code.updateLet! decl (← visitCode k)
      else if (← shouldExtractLetValue true decl.value) then
        let name ← performExtraction decl
        let decl ← decl.updateValue (.const name [] #[])
        return code.updateLet! decl (← visitCode k)
      else
        return code.updateLet! decl (← visitCode k)

    match decl.value with
    | .const ``Array.mkEmpty _ #[_, .fvar sizeId]
    | .const ``Array.emptyWithCapacity _ #[_, .fvar sizeId] =>
      if let some (.lit (.nat n)) ← findLetValue? (pu := .pure) sizeId then
        if n == 0 then
          let name ← performExtraction decl
          let decl ← decl.updateValue (.const name [] #[])
          return code.updateLet! decl (← visitCode k)
        else
          /-
          Extracting non-empty `Array` initializers on their own often isn't helpful because they
          will almost always be used later on by other declarations. This most frequently happens in
          one of two ways:
          1. They get mutated by some ordinary function in which case they will be copied from the
             persistent storage anyways.
          2. They get used by an `Array` literal which builds up an `Array.push` chain that we
             specifically pattern match on starting with an empty initializer of appropriate size.
          -/
          return code.updateLet! decl (← visitCode k)
      else
        visitLetDefault
    | _ => visitLetDefault
  | .fun decl k =>
    let decl ← decl.updateValue (← visitCode decl.value)
    return code.updateFun! decl (← visitCode k)
  | .jp decl k =>
    let decl ← decl.updateValue (← visitCode decl.value)
    return code.updateFun! decl (← visitCode k)
  | .cases cases =>
    let alts ← cases.alts.mapMonoM (fun alt => do return alt.updateCode (← visitCode alt.getCode))
    return code.updateAlts! alts
  | .jmp .. | .return _ | .unreach .. => return code
where
  performExtraction (decl : LetDecl .pure) : M Name := do
    let ⟨_, decls⟩ ← extractLetValue decl.value |>.run {}
    let decls := decls.reverse.push (.let decl)
    let decls ← decls.mapM Internalize.internalizeCodeDecl |>.run' {}
    let closedCode := attachCodeDecls decls (.return decls.back!.fvarId)
    let closedExpr := closedCode.toExpr
    let env ← getEnv
    if let some closedTermName := getClosedTermName? env closedExpr then
      eraseCode closedCode
      return closedTermName
    else
      let name := (← read).baseName ++ (`_closed).appendIndexAfter (← get).decls.size
      cacheClosedTermName env closedExpr name |> setEnv
      let decl := { name, levelParams := [], type := decl.type, params := #[],
                    value := .code closedCode, inlineAttr? := some .noinline }
      decl.saveMono
      modify fun s => { s with decls := s.decls.push decl }
      return name


end

def visitDecl (decl : Decl .pure) : M (Decl .pure) := do
  let value ← decl.value.mapCodeM visitCode
  return { decl with value }

end ExtractClosed

partial def Decl.extractClosed (decl : Decl .pure) (sccDecls : Array (Decl .pure)) :
    CompilerM (Array (Decl .pure)) := do
  let mut ⟨decl, s⟩ ← ExtractClosed.visitDecl decl |>.run { baseName := decl.name, sccDecls } |>.run {}
  if !s.decls.isEmpty then
    -- Closed term extraction might have left behind dead values.
    decl ← decl.elimDeadVars
  return s.decls.push decl

def extractClosed : Pass where
  phase := .mono
  name := `extractClosed
  run := fun decls => do
    if (← getConfig).extractClosed then
      decls.foldlM (init := #[]) fun newDecls decl =>
        return newDecls ++ (← decl.extractClosed decls)
    else
      return decls

builtin_initialize registerTraceClass `Compiler.extractClosed (inherited := true)

end Lean.Compiler.LCNF
