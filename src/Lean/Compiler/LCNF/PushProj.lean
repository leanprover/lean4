/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.Internalize

namespace Lean.Compiler.LCNF

/-!
Next steps:
- update variable names in go
- write module documentation explaining why things are like they are
- test
- benchmark
-/

mutual

partial def Cases.pushProjs (c : Cases .impure) (bs : Array (CodeDecl .impure)) : CompilerM (Code .impure) := do
  let altsUsed := c.alts.map (·.getCode.collectUsed)
  let ctxUsed := ({} : FVarIdHashSet) |>.insert c.discr
  let (bs, alts) ← go bs c.alts altsUsed #[] ctxUsed
  let alts ← alts.mapM (·.mapCodeM Code.pushProj)
  let c := c.updateAlts alts
  return attachCodeDecls bs (.cases c)
where
  /-
  Notes:
  - ctx are the variables we decided not to push
  - the two remaining sorris are collectFreeIndices on the entire body in the orig code,
    however I believe we can get away just collecting in CodeDecl
  -/
  go (bs : Array (CodeDecl .impure)) (alts : Array (Alt .impure)) (altsUsed : Array FVarIdHashSet)
      (ctx : Array (CodeDecl .impure)) (ctxUsed : FVarIdHashSet) :
      CompilerM (Array (CodeDecl .impure) × Array (Alt .impure)) :=
    if bs.isEmpty then
      return (ctx.reverse, alts)
    else
      let b := bs.back!
      let bs := bs.pop
      let done := return (bs.push b ++ ctx.reverse, alts)
      let skip := go bs alts altsUsed (ctx.push b) (b.collectUsed ctxUsed)
      let push (fvar : FVarId) : CompilerM (Array (CodeDecl .impure) × Array (Alt .impure)) := do
        if !ctxUsed.contains fvar then
          let alts ← alts.mapIdxM fun i alt => alt.mapCodeM fun k => do
            if altsUsed[i]!.contains fvar then
              return attachCodeDecls #[b] k
            else
              return k
          let altsUsed := altsUsed.map fun used => if used.contains fvar then (b.collectUsed used) else used
          go bs alts altsUsed ctx ctxUsed
        else
          skip
      match b with
      | .let decl =>
        match decl.value with
        | .uproj .. | .oproj .. | .sproj .. => push decl.fvarId
        -- TODO | .isShared .. => skip
        | _ => done
      | _ => done

partial def Code.pushProj (code : Code .impure) : CompilerM (Code .impure) := do
  go code #[]
where
  go (c : Code .impure) (bs : Array (CodeDecl .impure)) : CompilerM (Code .impure) := do
    match c with
    | .let decl k => go k (bs.push (.let decl))
    | .jp decl k =>
      let decl ← decl.updateValue (← decl.value.pushProj)
      go k (bs.push (.jp decl))
    | .uset var i y k _ =>
      go k (bs.push (.uset var i y))
    | .sset var i offset y ty k _ =>
      go k (bs.push (.sset var i offset y ty))
    | .cases c => c.pushProjs bs
    | .jmp .. | .return .. | .unreach .. =>
      return attachCodeDecls bs c

end

def Decl.pushProj (decl : Decl .impure) : CompilerM (Decl .impure) := do
  let value ← decl.value.mapCodeM (·.pushProj)
  let decl := { decl with value }
  decl.internalize

public def pushProj (occurrence : Nat) : Pass :=
  Pass.mkPerDeclaration `pushProj .impure Decl.pushProj occurrence

builtin_initialize
  registerTraceClass `Compiler.pushProj (inherited := true)

end Lean.Compiler.LCNF
