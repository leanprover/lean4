/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.Formatters.Lean.Parser.Term.Basic
public import Lean.Fmt.FmtM.Basic
meta import Lean.Meta.Tactic.Grind.Parser
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

public def fmtGrindIdentCnstr (tk : Syntax) (id : TSyntax `ident) (_semiTk? : Option Syntax)
    : FmtM TaggedDoc := do
  let tk ← fmt tk
  let id ← fmt id
  return Layouts.pseudoApplication #[tk, id]

public def fmtGrindIdentLtCnstr
    (tk : Syntax) (id : TSyntax `ident) (ltTk : Syntax) (n : TSyntax `num)
    (_semiTk? : Option Syntax)
    : FmtM TaggedDoc := do
  let tk ← fmt tk
  let id ← fmt id
  let lhs := Layouts.pseudoApplication #[tk, id]
  let ltTk ← fmt ltTk
  let n ← fmt n
  return Layouts.infixOperator #[lhs, ltTk, n]

public def fmtGrindLtCnstr
    (tk : Syntax) (ltTk : Syntax) (n : TSyntax `num) (_semiTk? : Option Syntax)
    : FmtM TaggedDoc := do
  let tk ← fmt tk
  let ltTk ← fmt ltTk
  let n ← fmt n
  return Layouts.infixOperator #[tk, ltTk, n]

public def fmtGrindTermCnstr (tk : Syntax) (t : TSyntax `term) (_semiTk? : Option Syntax)
    : FmtM TaggedDoc := do
  let tk ← fmt tk
  let t ← fmt t
  return Layouts.pseudoApplication #[tk, t]

public def fmtGrindEqCnstr
    (id : TSyntax `ident) (eqTk : Syntax) (rhs : TSyntax `term) (_semiTk? : Option Syntax)
    : FmtM TaggedDoc := do
  let id ← fmt id
  let eqTk ← fmt eqTk
  let rhs ← fmt rhs
  return Layouts.infixOperator #[id, eqTk, rhs]

@[builtin_fmt Lean.Parser.Command.GrindCnstr.isValue]
public def fmtGrindIsValue : Fmt := fun
  | `(Parser.Command.GrindCnstr.isValue| is_value%$isValueTk $id:ident $[;%$semiTk?]?) =>
    fmtGrindIdentCnstr isValueTk id semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.GrindCnstr.isStrictValue]
public def fmtGrindIsStrictValue : Fmt := fun
  | `(Parser.Command.GrindCnstr.isStrictValue| is_strict_value%$isStrictValueTk $id:ident $[;%$semiTk?]?) =>
    fmtGrindIdentCnstr isStrictValueTk id semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.GrindCnstr.notValue]
public def fmtGrindNotValue : Fmt := fun
  | `(Parser.Command.GrindCnstr.notValue| not_value%$notValueTk $id:ident $[;%$semiTk?]?) =>
    fmtGrindIdentCnstr notValueTk id semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.GrindCnstr.notStrictValue]
public def fmtGrindNotStrictValue : Fmt := fun
  | `(Parser.Command.GrindCnstr.notStrictValue| not_strict_value%$notStrictValueTk $id:ident $[;%$semiTk?]?) =>
    fmtGrindIdentCnstr notStrictValueTk id semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.GrindCnstr.isGround]
public def fmtGrindIsGround : Fmt := fun
  | `(Parser.Command.GrindCnstr.isGround| is_ground%$isGroundTk $id:ident $[;%$semiTk?]?) =>
    fmtGrindIdentCnstr isGroundTk id semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.GrindCnstr.sizeLt]
public def fmtGrindSizeLt : Fmt := fun
  | `(Parser.Command.GrindCnstr.sizeLt| size%$sizeTk $id:ident <%$ltTk $n:num $[;%$semiTk?]?) =>
    fmtGrindIdentLtCnstr sizeTk id ltTk n semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.GrindCnstr.depthLt]
public def fmtGrindDepthLt : Fmt := fun
  | `(Parser.Command.GrindCnstr.depthLt| depth%$depthTk $id:ident <%$ltTk $n:num $[;%$semiTk?]?) =>
    fmtGrindIdentLtCnstr depthTk id ltTk n semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.GrindCnstr.genLt]
public def fmtGrindGenLt : Fmt := fun
  | `(Parser.Command.GrindCnstr.genLt| gen%$genTk <%$ltTk $n:num $[;%$semiTk?]?) =>
    fmtGrindLtCnstr genTk ltTk n semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.GrindCnstr.maxInsts]
public def fmtGrindMaxInsts : Fmt := fun
  | `(Parser.Command.GrindCnstr.maxInsts| max_insts%$maxInstsTk <%$ltTk $n:num $[;%$semiTk?]?) =>
    fmtGrindLtCnstr maxInstsTk ltTk n semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.GrindCnstr.guard]
public def fmtGrindGuard : Fmt := fun
  | `(Parser.Command.GrindCnstr.guard| guard%$guardTk $t:term $[;%$semiTk?]?) =>
    fmtGrindTermCnstr guardTk t semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.GrindCnstr.check]
public def fmtGrindCheck : Fmt := fun
  | `(Parser.Command.GrindCnstr.check| check%$checkTk $t:term $[;%$semiTk?]?) =>
    fmtGrindTermCnstr checkTk t semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.GrindCnstr.notDefEq]
public def fmtGrindNotDefEq : Fmt := fun
  | `(Parser.Command.GrindCnstr.notDefEq| $id:ident =/=%$eqTk $t:term $[;%$semiTk?]?) =>
    fmtGrindEqCnstr id eqTk t semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.GrindCnstr.defEq]
public def fmtGrindDefEq : Fmt := fun
  | `(Parser.Command.GrindCnstr.defEq| $id:ident =?=%$eqTk $t:term $[;%$semiTk?]?) =>
    fmtGrindEqCnstr id eqTk t semiTk?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.grindPattern]
public def fmtGrindPattern : Fmt := fun
  | `(Parser.Command.grindPattern|
      $attrKind:attrKind grind_pattern%$grindPatternTk $[[%$lbTk? $patName?:ident ]%$rbTk?]? $declName:ident =>%$arrowTk
        $patterns:term,* $[where%$whereTk? $cnstrs?*]?) => do
    let attrKind ← fmt attrKind
    let grindPatternTk ← fmt grindPatternTk
    let lbTk? ← fmt? lbTk?
    let patName? ← fmt? patName?
    let rbTk? ← fmt? rbTk?
    let arrowTk ← fmt arrowTk
    let patterns ← fmtTSepArray patterns
    let whereTk? ← fmt? whereTk?
    let cnstrs := cnstrs?.getD #[]
    let cnstrs ← fmtArray cnstrs
    let tks := Layouts.spacedAtomic #[attrKind, grindPatternTk]
    let patNameGroup? := Layouts.bracketed lbTk? patName? rbTk? <| .dense
    let declName ← fmt declName
    let header := Layouts.blocks #[tks, patNameGroup?, declName]
    let patterns := Layouts.sepFill patterns
    let mainDecl := Layouts.assignmentDeclaration header arrowTk patterns
    let cnstrs := Layouts.lines cnstrs
    return Layouts.whereDeclaration mainDecl whereTk? cnstrs
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.initGrindNorm]
public def fmtInitGrindNorm : Fmt := fun
  | `(Parser.Command.initGrindNorm|
      init_grind_norm%$initGrindNormTk $preTheorems:ident* |%$pipeTk $postTheorems:ident*) => do
    let initGrindNormTk ← fmt initGrindNormTk
    let preTheorems ← fmtArray preTheorems
    let pipeTk ← fmt pipeTk
    let postTheorems ← fmtArray postTheorems
    return nested <| Layouts.horizontalOrVertical <|
      #[initGrindNormTk] ++ preTheorems ++ #[pipeTk] ++ postTheorems
  | _ =>
    throw .partialFormatter
