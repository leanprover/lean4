/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.WP.Tactic
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Attr.spec]
public def fmtSpecAttr : Fmt := fun
  | `(Parser.Attr.spec| spec%$specTk $[$prio?:prio]?) => do
    let specTk ← fmt specTk
    let prio? ← fmt? prio?
    return Layouts.pseudoApplication #[specTk, prio?]
  | _ => throw .partialFormatter

public def fmtInvariantAlt : Syntax → FmtM Layouts.Types.Alt := fun
  -- `·` also matches the ASCII `.` spelling.
  | `(Parser.Tactic.invariantDotAlt| ·%$cdotTk $inv:term) => do
    let cdotTk ← fmt cdotTk
    let inv ← fmt inv
    return Layouts.alt #[nested <| Layouts.softSpacedAtomic #[cdotTk, aligned inv]] empty empty
  | `(Parser.Tactic.invariantCaseAlt| |%$pipeTk $arg:caseArg =>%$arrowTk $inv:term) => do
    let pipeTk ← fmt pipeTk
    let arg ← fmt arg
    let arrowTk ← fmt arrowTk
    let inv ← fmt inv
    let lhs := nested <| Layouts.spacedAtomic #[pipeTk, arg]
    return Layouts.alt #[lhs] arrowTk inv
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.invariantAlts]
public def fmtInvariantAlts : Fmt := fun
  | `(Parser.Tactic.invariantAlts| $invariantsKW:invariantsKW $[$alts]*) => do
    let invariantsKW ← fmt invariantsKW
    let alts ← alts.mapM fmtInvariantAlt
    return Layouts.keywordPrefixedAlts invariantsKW alts
  | _ => throw .partialFormatter

public def fmtFrameAlt : Syntax → FmtM Layouts.Types.Alt := fun
  | `(Parser.Tactic.frameAlt| |%$pipeTk $f:ident $args:binderIdent* =>%$arrowTk $frame:term) => do
    let pipeTk ← fmt pipeTk
    let f ← fmt f
    let args ← fmtArray args
    let arrowTk ← fmt arrowTk
    let frame ← fmt frame
    let pat := Layouts.pseudoApplication <| #[f] ++ args
    let lhs := nested <| Layouts.spacedAtomic #[pipeTk, pat]
    return Layouts.alt #[lhs] arrowTk frame
  | _ => throw .partialFormatter

public def fmtVCGenHead (vcgenTk : Syntax) (cfg : TSyntax ``Parser.Tactic.optConfig)
    : FmtM TaggedDoc := do
  let vcgenTk ← fmt vcgenTk
  let cfg ← (← tacticOptConfigItems cfg).mapM fmt
  return Layouts.pseudoApplication <| #[vcgenTk] ++ cfg

public def fmtVCGenSimpArgs
    (lbTk? : Option Syntax) (args? : Option (Syntax.SepArray ",")) (rbTk? : Option Syntax)
    : FmtM TaggedDoc := do
  let lbTk? ← fmt? lbTk?
  let args ← fmtSepArray (args?.getD ⟨#[]⟩)
  let rbTk? ← fmt? rbTk?
  return Layouts.collection lbTk? args rbTk?

@[builtin_fmt Lean.Parser.Tactic.vcgenDischargeGrind]
public def fmtVCGenDischargeGrind : Fmt := fun
  | `(Parser.Tactic.vcgenDischargeGrind| $step:grind) => fmt step
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.vcgenDischargeTactic]
public def fmtVCGenDischargeTactic : Fmt := fun
  | `(Parser.Tactic.vcgenDischargeTactic| $tac:tactic) => fmt tac
  | _ => throw .partialFormatter

public def fmtVCGenLike
    (vcgenTk : Syntax) (cfg : TSyntax ``Parser.Tactic.optConfig) (lbTk? : Option Syntax)
    (args? : Option (Syntax.SepArray ",")) (rbTk? : Option Syntax) (untilTk? : Option Syntax)
    (untilProgram? : Option Syntax) (framesTk? : Option Syntax) (frameAlts : Array Syntax)
    (invariantAlts? : Option Syntax) (simpTk? : Option Syntax) (simpLbTk? : Option Syntax)
    (simpArgs? : Option (Syntax.SepArray ",")) (simpRbTk? : Option Syntax) (withTk? : Option Syntax)
    (discharge? : Option Syntax)
    : FmtM TaggedDoc := do
  let head ← fmtVCGenHead vcgenTk cfg
  let args ← fmtVCGenSimpArgs lbTk? args? rbTk?
  let untilTk? ← fmt? untilTk?
  let untilProgram? ← fmt? untilProgram?
  let framesTk? ← fmt? framesTk?
  let frameAlts ← frameAlts.mapM fmtFrameAlt
  let invariantAlts? ← fmt? invariantAlts?
  let simpTk? ← fmt? simpTk?
  let simpLbTk? ← fmt? simpLbTk?
  let simpArgs ← fmtSepArray (simpArgs?.getD ⟨#[]⟩)
  let simpRbTk? ← fmt? simpRbTk?
  let withTk? ← fmt? withTk?
  let discharge? ← fmt? discharge?
  let «until» := Layouts.keywordPrefixedTerm untilTk? untilProgram?
  let frames := Layouts.keywordPrefixedAlts framesTk? frameAlts
  let «simp» := Layouts.keywordPrefixedCollection simpTk? simpLbTk? simpArgs simpRbTk?
  let «with» := Layouts.keywordPrefixedTerm withTk? discharge?
  let framesBlock := { block := frames, hardNestedIfFirst := false }
  let invariantAltsBlock := { block := invariantAlts?, hardNestedIfFirst := false }
  return Layouts.blocks #[head, args, «until», framesBlock, invariantAltsBlock, «simp», «with»]

@[builtin_fmt Lean.Parser.Tactic.vcgen]
public def fmtVCGen : Fmt := fun
  | `(tactic| vcgen%$vcgenTk $cfg:optConfig $[[%$lbTk? $args?,* ]%$rbTk?]?
      $[until%$untilTk? $untilProgram?:term]?
      $[frames%$framesTk? $[$frameAlts?]*]?
      $[$invariantAlts?:invariantAlts]?
      $[simp%$simpTk? [%$simpLbTk? $simpArgs?,* ]%$simpRbTk?]?
      $[with%$withTk? $discharge?:vcgenDischarge]?) =>
    fmtVCGenLike vcgenTk cfg lbTk? args? rbTk? untilTk? untilProgram? framesTk?
      (frameAlts?.getD #[]) invariantAlts? simpTk? simpLbTk? simpArgs? simpRbTk? withTk? discharge?
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.Grind.vcgen]
public def fmtGrindVCGen : Fmt := fun
  | `(Parser.Tactic.Grind.vcgen| vcgen%$vcgenTk $cfg:optConfig $[[%$lbTk? $args?,* ]%$rbTk?]?
      $[until%$untilTk? $untilProgram?:term]?
      $[frames%$framesTk? $[$frameAlts?]*]?
      $[$invariantAlts?:invariantAlts]?
      $[simp%$simpTk? [%$simpLbTk? $simpArgs?,* ]%$simpRbTk?]?) =>
    fmtVCGenLike vcgenTk cfg lbTk? args? rbTk? untilTk? untilProgram? framesTk?
      (frameAlts?.getD #[]) invariantAlts? simpTk? simpLbTk? simpArgs? simpRbTk? none none
  | _ => throw .partialFormatter
