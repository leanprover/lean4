/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Ext
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Attr.extIff]
public def fmtExtIff : Fmt := fun
  | `(Parser.Attr.extIff| (%$lbTk iff%$iffTk :=%$colonEqTk false%$falseTk )%$rbTk) =>
    fmtNamedArgumentTerm lbTk iffTk colonEqTk falseTk rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.extFlat]
public def fmtExtFlat : Fmt := fun
  | `(Parser.Attr.extFlat| (%$lbTk flat%$flatTk :=%$colonEqTk false%$falseTk )%$rbTk) =>
    fmtNamedArgumentTerm lbTk flatTk colonEqTk falseTk rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.ext]
public def fmtExtAttr : Fmt := fun
  | `(Parser.Attr.ext| ext%$extTk $[$extIff?:extIff]? $[$extFlat?:extFlat]? $[$prio?:prio]?) => do
    let extTk ← fmt extTk
    let extIff? ← fmt? extIff?
    let extFlat? ← fmt? extFlat?
    let prio? ← fmt? prio?
    return Layouts.pseudoApplication #[extTk, extIff?, extFlat?, prio?]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Elab.Tactic.Ext.ext]
public def fmtTacticExt : Fmt := fun
  | `(tactic| ext%$extTk $pats:rintroPat* $[:%$colonTk? $depth?:num]?) => do
    let extTk ← fmt extTk
    let pats ← fmtArray pats
    let colonTk? ← fmt? colonTk?
    let depth? ← fmt? depth?
    let pats := Layouts.fill pats
    let annotatedPats := Layouts.typeAscription pats colonTk? depth?
    return Layouts.pseudoApplication #[extTk, annotatedPats]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Elab.Tactic.Ext.tacticExt1___]
public def fmtTacticExt1 : Fmt := fun
  | `(tactic| ext1%$ext1Tk $pats:rintroPat*) => do
    let ext1Tk ← fmt ext1Tk
    let pats ← fmtArray pats
    return Layouts.pseudoApplication <| #[ext1Tk] ++ pats
  | _ => throw .partialFormatter
