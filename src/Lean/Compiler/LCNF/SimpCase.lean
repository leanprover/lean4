/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.AlphaEqv
import Init.Omega

namespace Lean.Compiler.LCNF


-- TODO: dedup with simp

/--
Return the alternative in `alts` whose body appears in most arms,
and the number of occurrences.
We use this function to decide whether to create a `.default` case
or not.
-/
private def getMaxOccs (alts : Array (Alt .impure)) : Alt .impure × Nat := Id.run do
  let mut maxAlt := alts[0]!
  let mut max    := getNumOccsOf alts 0
  for h : i in 1...alts.size do
    let curr := getNumOccsOf alts i
    if curr > max then
       maxAlt := alts[i]
       max    := curr
  return (maxAlt, max)
where
  /--
  Return the number of occurrences of `alts[i]` in `alts`.
  We use alpha equivalence.
  Note that the number of occurrences can be greater than 1 only when
  the alternative does not depend on field parameters
  -/
  getNumOccsOf (alts : Array (Alt .impure)) (i : Nat) : Nat := Id.run do
    let code := alts[i]!.getCode
    let mut n := 1
    for h : j in (i+1)...alts.size do
      if Code.alphaEqv alts[j].getCode code then
        n := n+1
    return n

/--
Add a default case to the given `cases` alternatives if there
are alternatives with equivalent (aka alpha equivalent) right hand sides.
-/
def addDefaultAlt (alts : Array (Alt .impure)) : CompilerM (Array (Alt .impure)) := do
  if alts.size <= 1 || alts.any (· matches .default ..) then
    return alts
  else
    let (max, noccs) := getMaxOccs alts
    if noccs == 1 then
      return alts
    else
      let mut altsNew := #[]
      let mut first := true
      for alt in alts do
        if Code.alphaEqv alt.getCode max.getCode then
          let .ctorAlt _ k := alt | unreachable!
          unless first do
            eraseCode k
          first := false
        else
          altsNew := altsNew.push alt
      return altsNew.push (.default max.getCode)

def filterUnreachable (alts : Array (Alt .impure)) : Array (Alt .impure) :=
  alts.filter (fun alt => !alt.getCode matches .unreach ..)

def simplifyCases (c : Cases .impure) : CompilerM (Code .impure) := do
  let alts := filterUnreachable c.alts
  let alts ← addDefaultAlt alts
  if alts.size == 0 then
    -- TODO: trace this out
    return .unreach c.resultType
  else if h : alts.size = 1 then
    return alts[0].getCode
  else
    return .cases <| c.updateAlts alts

partial def Code.simpCase (code : Code .impure) : CompilerM (Code .impure) := do
  match code with
  | .cases c =>
    let alts ← c.alts.mapMonoM (fun alt => return alt.updateCode (← alt.getCode.simpCase))
    simplifyCases (c.updateAlts alts)
  | .jp decl k =>
    let decl ← decl.updateValue (← decl.value.simpCase)
    return code.updateFun! decl (← k.simpCase)
  | .return .. | .jmp .. | .unreach .. => return code
  | .let _ k | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ =>
    return code.updateCont! (← k.simpCase)

def Decl.simpCase (decl : Decl .impure) : CompilerM (Decl .impure) := do
  let value ← decl.value.mapCodeM (·.simpCase)
  return { decl with value }

public def simpCase : Pass :=
  Pass.mkPerDeclaration `simpCase .impure Decl.simpCase 0

builtin_initialize
  registerTraceClass `Compiler.simpCase (inherited := true)

end Lean.Compiler.LCNF
