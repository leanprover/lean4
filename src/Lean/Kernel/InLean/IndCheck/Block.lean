/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.IndCheck.Rec

/-!
# InLean's inductive checker: the block

The inductive declaration's path: the unverified generator (`Ind.genInductive`)
produces the block's constants as the official kernel would; they are the
stored block, and con-leche's checked job runs on them — twin of
`checkIndDeclC` (`Cached/ParsedC.lean`) and `checkBlockKS`/`checkBlockPassS`/
`checkBlockTailS` (`Cached/CheckerC.lean`): the pinned basis blocks, the
declared parameter count, the recogniser, the formers, the constructors,
the classes, nested positivity and its seeds, the index sorts, the
regeneration of every recursor (`genRecCheck`) and the stored recursors
against it up to definitional equality (`storedRecsCheck`), the
projection tables.  What InLean installs is the generator's constants,
exactly; the job only decides whether they are accepted.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

namespace IC

/-- Twin of `checkBlockKS` (with `checkBlockPassS` and `checkBlockTailS`). -/
def checkBlock (j : Job) (env : Kernel.Environment) (block : List SCI) (p₀ : BlockShape) : M Unit := do
  unless nodup (p₀.allCtors.map (·.1.name)) && nodup p₀.memberNames do
    throwInvalid "direct rec: duplicate constructor"
  flush
  -- the pass
  let (env₁, cvTas, p) ← checkBlockInds j env p₀
  flush
  let (ctorsAs, sortsss) ← checkBlockCtors j env₁ env₁ p (p.members.zip cvTas)
  let (ctx, holes) ← blockNestCtx p cvTas env₁
  let (rd, Ms) ← checkBlockClasses j env₁ p ctx.params ctorsAs
  let (kinds, _nfs, pos) ← checkBlockPositivity j env₁ p cvTas ctorsAs
  let st ← nestSeeds j env₁ ctx (← classSeeds ctx holes Ms) pos
  -- the tail
  let _ ← checkBlockIdxSorts j env₁ p (p.members.zip cvTas)
  let fe₂ ← consBlockCtors j ctorsAs env₁
  flush
  let out ← genRecCheck j fe₂ p (blockNestedBit p kinds) ctx.params st.ctorNfs.toList rd Ms cvTas block
  -- the regenerated recursors consed (`blockRecInfosTF`), the stored ones compared there
  let mut feG := fe₂
  for (cv, M', rhss) in out do
    feG ← j.push feG cv.name cv.type (some (genRules M' rhss))
  flush
  storedRecsCheck j feG p.recs out
  flush
  checkBlockTables p feG (p.members.zip (ctorsAs.zip sortsss))

/-- Twin of `checkShapelessS`: the formers checked as constants, then a
positive decline. -/
def checkShapeless (j : Job) (env : Kernel.Environment) (block : List SCI) : M Unit := do
  for c in block do
    if let .ind cv := c then j.checkConstantVal env cv
  throwDeclined s!"inductive block {(block.head?.map (·.name)).getD .anonymous}: shape not recognised"

/-- A generated constant's terms are in range (`EO.inRange`). -/
def constInRange : ConstantInfo → Bool
  | .recInfo v => EO.inRange v.type && v.rules.all fun r => EO.inRange r.rhs
  | ci => EO.inRange ci.type

/-- **An inductive declaration**: generate (unverified, `Ind.genInductive`),
then con-leche's checks on the generated block (twin of `checkIndDeclC`).
An unsafe block is checked as the official kernel checks one (positivity
and the rest of the installer's soundness checks skipped: each constant's
type is checked at the unsafe safety). -/
def checkInductiveDecl (μ : CheckMode) (addConst : Kernel.Environment → ConstantInfo → Kernel.Environment)
    (lps : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool) : M Added := do
  let env := (← read).env
  let gen ← Ind.genInductive μ addConst lps nparams types isUnsafe
  -- the generator is unverified: what it hands over is checked to be in range
  --, so its terms' cached fields mean what the proof says they do
  for ci in gen.consts do
    unless constInRange ci do
      throwInternal s!"too many bound variables in generated constant {ci.name}"
  let block := storedBlock gen.consts
  let mut genMap : Std.HashMap Name ConstantInfo := {}
  for ci in gen.consts do genMap := genMap.insert ci.name ci
  let j : Job := { μ, addConst, gen := genMap }
  if isUnsafe then
    withReader (fun c => { c with safety := .unsafe }) do
      let mut e := env
      for ci in gen.consts do
        match ci with
        | .inductInfo _ | .ctorInfo _ =>
          j.checkConstantVal e (ofCI ci)
          e := addConst e ci
        | _ => e := addConst e ci
    return gen
  unless andPinOk nparams block do
    throwInvalid "a declaration of And that is not the pinned And"
  if basisPinHit block then
    -- the pinned basis block: installed as the pin (`checkBasisDeclC`), duplicates refused
    for c in block do
      if (env.find? c.name).isSome then throwInvalid s!"duplicate declaration {c.name}"
    return gen
  unless indParamsOk nparams block do throwInvalid "number of parameters mismatch"
  match blockParts? nparams block with
  | some p => checkBlock j env block p
  | none => checkShapeless j env block
  return gen

end IC

end Lean.Kernel.InLean
