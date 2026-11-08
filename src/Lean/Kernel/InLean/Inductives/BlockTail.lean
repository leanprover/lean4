/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Inductives.StreamRecs
public import Lean.Kernel.InLean.CheckerC

/-!
# InLean's inductive check: the block job

Twin of `ConLeche.Kernel.Inductives.BlockTail` and of its cached
instantiation in `ConLeche.Cached.CheckerC` (`sharedOpsC`,
`shadowOpsC`, `checkBlockPassS`, `checkBlockTailS`, `reduceMembersS`,
`checkBlockKS`): the members reduced, the formers and constructors checked,
the classes read, nested positivity and its seeds, the index sorts, every
recursor regenerated and the block's compared with it, the K flags, the
projection tables.  The core's memos are flushed where con-leche's are.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-- Twin of `BlockPass`. -/
structure BlockPass where
  env₁ : FEnv
  p : BlockShape
  kinds : List (List (List NestFieldKind))
  params : List Expr
  rd : ClassRead
  cls : List TargetMajor
  tbl : Array NestCtorNf

/-- Twin of `declinedAtDefinition`. -/
def declinedAtDefinition : List Name :=
  [stringOfListName, listNilName, listConsName, charOfNatName, boolName]

/-- Twin of `structWalkersC`. -/
def structWalkersC : StructWalkers := ⟨constsResolveF, structProjBodies⟩

section
variable (mode : CheckMode)

/-- Twin of `sharedOpsC`: the core at `fe` (the environment argument is the
one the ops were built at). -/
def sharedOpsC (fe : FEnv) : CheckerOps where
  inferType _ d e := opInfer mode fe d e
  isDefEq _ d a b := opDefeq mode fe d a b
  ensureSort _ d e := opSort mode fe d e
  whnf _ d e := opWhnf mode fe d e

/-- Twin of `sharedOpsRuleR`. -/
def sharedOpsRuleR (fe : FEnv) : CheckerOps :=
  { sharedOpsC mode fe with
    inferType := fun _ d e => do
      flushC
      let t ← opInfer mode fe d e
      flushC
      pure t }

/-- Twin of `shadowOpsC`. -/
def shadowOpsC : ShadowOps :=
  ⟨sharedOpsC mode, sharedOpsRuleR mode, flushC, structWalkersC, classFeROvl⟩

/-- Twin of `checkBlockPassS`. -/
def checkBlockPassS (fe : FEnv) (p₀ : BlockShape) (isRec : Bool) : CheckCM BlockPass := do
  let (fe₁, p₁) ← checkBlockIndsF (sharedOpsC mode fe) fe p₀ isRec
  flushC
  checkBlockCtorsF (sharedOpsC mode fe₁) fe₁ fe₁ p₁ p₁.members
  let (ctx, holes) ← blockNestCtx p₁ fe₁
  let (rd, Ms) ← checkBlockClasses (sharedOpsC mode fe₁) fe₁ p₁ ctx.params
  let (outs, pos) ← checkBlockPositivity (sharedOpsC mode fe₁) fe₁ p₁
  let st ← nestSeeds (sharedOpsC mode fe₁) fe₁ ctx (← classSeeds ctx holes Ms) pos
  pure ⟨fe₁, p₁, nestOutKinds outs, ctx.params, rd, Ms, st.ctorNfs⟩

/-- Twin of `checkBlockTailS`. -/
def checkBlockTailS (block : List ConstantInfo) (q : BlockPass) : CheckCM Unit :=
  match q with
  | ⟨env₁, p, kinds, params, rd, cls, tbl⟩ => do
  checkBlockIdxSortsF (sharedOpsC mode env₁) env₁ p p.members
  let fe₂ := consBlockCtorsF p env₁
  flushC
  let out ← genRecCheck (shadowOpsC mode) fe₂ p
    (blockNestedBit p kinds) params tbl.toList rd cls block
  streamKCheck p p.recs out
  let feG := fe₂.pushAll (blockRecInfosTF p 0 out)
  flushC
  streamRecsCheck (sharedOpsC mode feG) structWalkersC feG p.recs out
  flushC
  checkBlockTablesF structWalkersC p fe₂ p.members

/-- Twin of `reduceMemberS`. -/
def reduceMemberS (fe : FEnv) (ms : MemberShape) (nP : Nat) : CheckCM MemberShape :=
  if formerDefHeaded ms.cvT then do
    if declinedAtDefinition.contains ms.cvT.name then
      throw (.notImplemented s!"this family stored at a definition ({ms.cvT.name})")
    else do
      checkConstantValF (sharedOpsC mode fe) fe ms.cvT
      let cvR ← reducedFormer (sharedOpsC mode fe) fe ms.cvT (nP + ms.nIdx)
      unless ← (sharedOpsC mode fe).isDefEq fe 0 ms.cvT.type cvR.type do
        throw (.invalid "direct sum: a type former's declared type and its reduct differ")
      pure { ms with cvT := cvR }
  else pure ms

/-- Twin of `reduceMembersS`. -/
def reduceMembersS (fe : FEnv) (nP : Nat) : List MemberShape → CheckCM (List MemberShape)
  | [] => pure []
  | ms :: rest => do
    flushC
    let ms' ← reduceMemberS mode fe ms nP
    let rest' ← reduceMembersS fe nP rest
    pure (ms' :: rest')

/-- Twin of `checkBlockKS`.  con-leche returns the environment with the
block's constants pushed; InLean's declaration step returns the constants a
declaration adds (`Added`), here the block itself, so this returns nothing. -/
def checkBlockKS (fe : FEnv) (block : List ConstantInfo) (p₀ : BlockShape) : CheckCM Unit := do
  unless namesNodup (p₀.allCtors.map (·.1.name)) && namesNodup p₀.memberNames do
    throw (.invalid "direct rec: duplicate constructor")
  unless !p₀.memberNames.contains boolTrueName && !p₀.memberNames.contains boolFalseName do
    throw (.invalid "direct rec: a family at a `Bool` constructor's name")
  let ms ← reduceMembersS mode fe p₀.nP p₀.members
  flushC
  let q ← checkBlockPassS mode fe { p₀ with members := ms } (blockIsRec p₀)
  checkBlockTailS mode block q

end

end Lean.Kernel.InLean
