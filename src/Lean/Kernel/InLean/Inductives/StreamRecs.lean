/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Inductives.GenRec

/-!
# InLean's inductive check: the stream's recursors against the generated ones

Twin of `ConLeche.Kernel.Inductives.StreamRecs`: each recursor the block
declares compared with the one generated from its classes (type, rules, firing
data and K flag).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

variable (mode : CheckMode)

/-- Twin of `recDomsAt`. -/
def recDomsAt (env : FEnv) (rec : Name) (sfvs gfvs : List Expr) :
    Nat → Nat → CheckCM Unit
  | _, 0 => pure ()
  | j, k + 1 => do
    let a ← unwrapOr sfvs[j]? (.internal "stored recursor: domain index")
    let b ← unwrapOr gfvs[j]? (.internal "stored recursor: domain index")
    unless ← opDefeq mode env j (← fvarTypeD a) (← fvarTypeD b) do
      throw (.invalid s!"the type of the recursor {rec} is not the generated one: the \
        domain of binder {j} differs")
    recDomsAt env rec sfvs gfvs (j + 1) k

/-- Twin of `recTyOpened`. -/
def recTyOpened (env : FEnv) (rec : Name) (n : Nat) :
    Option (List Expr × Expr) → Option (List Expr × Expr) → CheckCM Unit
  | some (sfvs, srest), some (gfvs, grest) => do
    recDomsAt mode env rec sfvs gfvs 0 n
    unless ← opDefeq mode env n srest grest do
      throw (.invalid s!"the type of the recursor {rec} is not the generated one: its body \
        after the major differs")
  | none, _ =>
    throw (.invalid s!"the type of the recursor {rec} is not the generated one: it has fewer \
      than {n} binders")
  | some _, none =>
    throw (.internal s!"the generated type of the recursor {rec} has fewer than {n} binders")

/-- Twin of `recTyCheck`. -/
def recTyCheck (fe : FEnv) (rec : Name)
    (lps : List Name) (n : Nat) (s g : Expr) : CheckCM Unit := do
  unless !s.hasLooseBVars && !s.hasFVar && !g.hasFVar do
    throw (.invalid s!"the type of the recursor {rec} is not closed")
  unless ← allLevelParamsDefined lps s do
    throw (.invalid s!"undeclared universe parameter in the type of the recursor {rec}")
  unless ← constsResolveF fe s do
    throw (unresolvedConstsErrorL fe true s!"the type of the recursor {rec}" s)
  let st ← opInfer mode fe 0 s
  let _ ← opSort mode fe 0 st
  recTyOpened mode fe rec n (← openPisAtFvars n s 0) (← openPisAtFvars n g 0)

/-- Twin of `ruleAgree`. -/
def ruleAgree (fe : FEnv) (rec ctor : Name)
    (lps : List Name) (s g : Expr) : CheckCM Unit := do
  unless !s.hasLooseBVars && !s.hasFVar && !g.hasFVar do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side that is \
      not closed")
  unless ← allLevelParamsDefined lps s do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has an undeclared universe \
      parameter")
  unless ← constsResolveF fe s do
    throw (unresolvedConstsErrorL fe true s!"the recursor {rec}'s rule for {ctor}" s)
  let ts ← opInfer mode fe 0 s
  let tg ← opInfer mode fe 0 g
  unless ← opDefeq mode fe 0 ts tg do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side whose \
      type is not the generated one's")
  unless ← opDefeq mode fe 0 s g do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side that is \
      not definitionally equal to the generated one")

/-- Twin of `streamNestedOk`. -/
def streamNestedOk (ty : Expr) (mI rP : Nat) : RecRuleFire → Bool
  | .plain => true
  | .levels _ => true
  | .nested lvls pins =>
    match (stripPis mI ty).map (fun (p : List Expr × Expr) => EO.stripTop p.2) with
    | some (.forallE _ dom _ _) =>
      (match dom.getAppFnT with
       | .const _ us => us == lvls
       | _ => false) &&
      appArgs dom ==
        pins.map (EO.liftLooseBVars · 0 (mI - rP)) ++
          (List.range (mI - rP)).map (fun i => mkBvar (mI - rP - 1 - i))
    | _ => false

/-- Twin of `generatedFire`. -/
def generatedFire (M : TargetMajor) (rP : Nat) : RecRuleFire :=
  match M.member with
  | none => auxRuleFire M rP
  | some _ => .plain

/-- Twin of `streamRulesShape`. -/
def streamRulesShape (rec : Name) : List RecursorRule → List (ConstantVal × Nat) → CheckCM Unit
  | [], [] => pure ()
  | r :: rs, c :: cs => do
    unless r.ctor == c.1.name && r.nfields == c.2 do
      throw (.invalid s!"the recursor {rec}'s rule for {r.ctor} is not the generated one's \
        (constructor {c.1.name}, {c.2} fields)")
    streamRulesShape rec rs cs
  | rs, cs =>
    throw (.invalid s!"the recursor {rec} carries {rs.length} more or fewer rules than the \
      generated one ({cs.length} unmatched)")

/-- Twin of `streamRulesCheck`. -/
def streamRulesCheck (fe : FEnv) (rec : Name)
    (lps : List Name) : List RecursorRule → List Expr → CheckCM Unit
  | r :: rs, g :: gs => do
    unless r.rhs == g do
      ruleAgree mode fe rec r.ctor lps r.rhs g
    streamRulesCheck fe rec lps rs gs
  | [], [] => pure ()
  | _, _ => throw (.internal s!"the recursor {rec}: the generated rules are not one per stored rule")

/-- Twin of `streamRecCompare`. -/
def streamRecCompare (fe : FEnv) (rc : RecShape)
    (g : ConstantVal × TargetMajor × List Expr) : CheckCM Unit := do
  unless rc.cvR.type == g.1.type do
    recTyCheck mode fe g.1.name g.1.levelParams (rc.mI + 1) rc.cvR.type g.1.type
  streamRulesCheck mode fe g.1.name g.1.levelParams rc.rules g.2.2

/-- Twin of `streamRecCheck`. -/
def streamRecCheck (fe : FEnv) (rc : RecShape) (g : ConstantVal × TargetMajor × List Expr) : CheckCM Unit := do
  streamRulesShape rc.cvR.name rc.rules g.2.1.ctors
  unless streamNestedOk rc.cvR.type rc.mI rc.rP (generatedFire g.2.1 rc.rP) do
    throw (.invalid s!"the recursor {rc.cvR.name}'s stored type does not apply its \
      major's container at the generated firing data")
  streamRecCompare mode fe rc g

/-- Twin of `streamRecsCheck`. -/
def streamRecsCheck (fe : FEnv) : List RecShape → List (ConstantVal × TargetMajor × List Expr) → CheckCM Unit
  | rc :: rcs, g :: gs => do
    streamRecCheck mode fe rc g
    streamRecsCheck fe rcs gs
  | [], [] => pure ()
  | _, _ => throw (.internal "stored recursors: the generated family is not the records'")

/-- Twin of `streamKCheck`. -/
def streamKCheck (p : BlockShape) :
    List RecShape → List (ConstantVal × TargetMajor × List Expr) → CheckCM Unit
  | rc :: rcs, g :: gs => do
    unless rc.isK == recKExpected p g.2.1 do
      throw (.invalid s!"recursor {rc.cvR.name} declares k := {rc.isK}; the generated recursor \
        of this block is{if recKExpected p g.2.1 then "" else " not"} K-like")
    streamKCheck p rcs gs
  | _, _ => pure ()

end Lean.Kernel.InLean
