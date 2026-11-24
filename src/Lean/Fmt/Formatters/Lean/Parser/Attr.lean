/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Parser.Attr
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Attr.simple]
public def fmtSimpleAttr : Fmt := fun
  | `(Parser.Attr.simple| $id:ident $[$arg?]?) => do
    let id ← fmt id
    let arg? ← fmt? arg?
    return Layouts.pseudoApplication #[id, arg?]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.macro]
public def fmtMacroAttr : Fmt := fun
  | `(Parser.Attr.macro| macro%$macroTk $id:ident) => do
    let macroTk ← fmt macroTk
    let id ← fmt id
    return Layouts.pseudoApplication #[macroTk, id]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.export]
public def fmtExportAttr : Fmt := fun
  | `(Parser.Attr.export| export%$exportTk $id:ident) => do
    let exportTk ← fmt exportTk
    let id ← fmt id
    return Layouts.pseudoApplication #[exportTk, id]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.recursor]
public def fmtRecursorAttr : Fmt := fun
  | `(Parser.Attr.recursor| recursor%$recursorTk $val:num) => do
    let recursorTk ← fmt recursorTk
    let val ← fmt val
    return Layouts.pseudoApplication #[recursorTk, val]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.class]
public def fmtClassAttr : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Attr.instance]
public def fmtInstanceAttr : Fmt := fun
  | `(Parser.Attr.instance| instance%$instanceTk $[$prio?:prio]?) => do
    let instanceTk ← fmt instanceTk
    let prio? ← fmt? prio?
    return Layouts.pseudoApplication #[instanceTk, prio?]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.default_instance]
public def fmtDefaultInstanceAttr : Fmt := fun
  | `(Parser.Attr.default_instance| default_instance%$instanceTk $[$prio?:prio]?) => do
    let instanceTk ← fmt instanceTk
    let prio? ← fmt? prio?
    return Layouts.pseudoApplication #[instanceTk, prio?]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.specialize]
public def fmtSpecializeAttr : Fmt := fun
  | `(Parser.Attr.specialize| specialize%$specializeTk $args*) => do
    let specializeTk ← fmt specializeTk
    let args ← fmtArray args
    return Layouts.pseudoApplication <| #[specializeTk] ++ args
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.externEntry]
public def fmtExternEntry : Fmt := fun
  | `(Parser.Attr.externEntry| $[$id?]? $[inline%$inlineTk?]? $val:str) => do
    let id? ← fmt? id?
    let inlineTk? ← fmt? inlineTk?
    let val ← fmt val
    return Layouts.pseudoApplication #[id?, inlineTk?, val]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.extern]
public def fmtExternAttr : Fmt := fun
  | `(Parser.Attr.extern| extern%$externTk $entries*) => do
    let externTk ← fmt externTk
    let entries ← fmtArray entries
    return Layouts.pseudoApplication <| #[externTk] ++ entries
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.tactic_alt]
public def fmtTacticAltAttr : Fmt := fun
  | `(Parser.Attr.tactic_alt| tactic_alt%$tacticAltTk $id:ident) => do
    let tacticAltTk ← fmt tacticAltTk
    let id ← fmt id
    return Layouts.pseudoApplication #[tacticAltTk, id]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.tactic_tag]
public def fmtTacticTagAttr : Fmt := fun
  | `(Parser.Attr.tactic_tag| tactic_tag%$tacticTagTk $ids:ident*) => do
    let tacticTagTk ← fmt tacticTagTk
    let ids ← fmtArray ids
    return Layouts.pseudoApplication <| #[tacticTagTk] ++ ids
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.tactic_name]
public def fmtTacticNameAttr : Fmt := fun
  | `(Parser.Attr.tactic_name| tactic_name%$tacticNameTk $name) => do
    let tacticNameTk ← fmt tacticNameTk
    let name ← fmt name
    return Layouts.pseudoApplication #[tacticNameTk, name]
  | _ => throw .partialFormatter
