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

Twin of the cached block driver in `ConLeche.Cached.CheckerC`
(`checkBlockPassS`, `checkBlockTailS`, `reduceMembersS`, `checkBlockKS`): the members reduced, the formers and constructors checked,
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

section
variable (mode : CheckMode)

/-- Twin of `checkBlockPassS`. -/
def checkBlockPassS (fe : FEnv) (p₀ : BlockShape) (isRec : Bool) : CheckCM BlockPass := do
  let (fe₁, p₁) ← checkBlockIndsC mode fe p₀ isRec
  flushC
  checkBlockCtorsC mode fe₁ fe₁ p₁ p₁.members
  let (ctx, holes) ← blockNestCtx p₁ fe₁
  let (rd, Ms) ← checkBlockClasses mode fe₁ p₁ ctx.params
  let (outs, pos) ← checkBlockPositivity mode fe₁ p₁
  let st ← nestSeeds mode fe₁ ctx (← classSeeds ctx holes Ms) pos
  pure ⟨fe₁, p₁, nestOutKinds outs, ctx.params, rd, Ms, st.ctorNfs⟩

/-- Twin of `checkBlockTailS`. -/
def checkBlockTailS (block : List ConstantInfo) (q : BlockPass) (Q : List ProjTable) :
    CheckCM Unit :=
  match q with
  | ⟨env₁, p, kinds, params, rd, cls, tbl⟩ => do
  checkBlockIdxSortsC mode env₁ p p.members
  let fe₂ := consBlockCtorsF p env₁
  flushC
  let out ← genRecCheck mode fe₂ p
    (blockNestedBit p kinds) params tbl.toList rd cls block
  streamKCheck p p.recs out
  let feG := fe₂.pushAll (blockRecInfosTF p 0 out)
  flushC
  streamRecsCheck mode feG p.recs out
  flushC
  checkBlockTablesC fe₂ Q

/-- Twin of `reduceMemberS`. -/
def reduceMemberS (fe : FEnv) (ms : MemberShape) (nP : Nat) : CheckCM MemberShape :=
  if formerDefHeaded ms.cvT then do
    if declinedAtDefinition.contains ms.cvT.name then
      throw (.notImplemented s!"this family stored at a definition ({ms.cvT.name})")
    else do
      checkConstantValC mode fe ms.cvT
      let cvR ← reducedFormer mode fe ms.cvT (nP + ms.nIdx)
      unless ← opDefeq mode fe 0 ms.cvT.type cvR.type do
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
  let Q ← unwrapOr (blockTables p₀ p₀.members) (.internal "direct structure: projection bodies")
  checkBlockTailS mode block q Q

end

end Lean.Kernel.InLean
