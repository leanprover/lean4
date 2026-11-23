/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Grind.Lint
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Grind.grindLintCheck]
public def fmtGrindLintCheck : Fmt := fun
  | `(Grind.grindLintCheck|
      #grind_lint%$grindLintTk check%$checkTk $cfgItems:configItem*
        $[in%$inTk? $[module%$moduleTk?]? $ids?:ident*]?) => do
    let grindLintTk ← fmt grindLintTk
    let checkTk ← fmt checkTk
    let cfgItems ← fmtArray cfgItems
    let inTk? ← fmt? inTk?
    let moduleTk? ← fmt? moduleTk?.join
    let ids ← fmtArray (ids?.getD #[])
    let keyword := Layouts.spacedAtomic #[grindLintTk, checkTk]
    let check := Layouts.pseudoApplication (#[keyword] ++ cfgItems)
    let inKeyword := Layouts.spacedAtomic #[inTk?, moduleTk?]
    let «in» := Layouts.pseudoApplication (#[inKeyword] ++ ids)
    return Layouts.pseudoApplication #[check, «in»]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Grind.grindLintInspect]
public def fmtGrindLintInspect : Fmt := fun
  | `(Grind.grindLintInspect|
      #grind_lint%$grindLintTk inspect%$inspectTk $cfgItems:configItem* $ids:ident*) => do
    let grindLintTk ← fmt grindLintTk
    let inspectTk ← fmt inspectTk
    let cfgItems ← fmtArray cfgItems
    let ids ← fmtArray ids
    let keyword := Layouts.spacedAtomic #[grindLintTk, inspectTk]
    let inspect := Layouts.pseudoApplication (#[keyword] ++ cfgItems)
    return Layouts.pseudoApplication (#[inspect] ++ ids)
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Grind.grindLintMute]
public def fmtGrindLintMute : Fmt := fun
  | `(Grind.grindLintMute| #grind_lint%$grindLintTk mute%$muteTk $ids:ident*) => do
    let grindLintTk ← fmt grindLintTk
    let muteTk ← fmt muteTk
    let ids ← fmtArray ids
    let keyword := Layouts.spacedAtomic #[grindLintTk, muteTk]
    return Layouts.pseudoApplication (#[keyword] ++ ids)
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Grind.grindLintSkip]
public def fmtGrindLintSkip : Fmt := fun
  | `(Grind.grindLintSkip|
      #grind_lint%$grindLintTk skip%$skipTk $[suffix%$suffixTk?]? $ids:ident*) => do
    let grindLintTk ← fmt grindLintTk
    let skipTk ← fmt skipTk
    let suffixTk? ← fmt? suffixTk?
    let ids ← fmtArray ids
    let keyword := Layouts.spacedAtomic #[grindLintTk, skipTk, suffixTk?]
    return Layouts.pseudoApplication (#[keyword] ++ ids)
  | _ => throw .partialFormatter
