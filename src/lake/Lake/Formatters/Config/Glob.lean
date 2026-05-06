/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lake.Config.Glob
import Init.Data

open Lean Lean.Fmt

namespace Lake.Formatters

@[builtin_fmt Lake.«term__.*»]
public def fmtGlobAndSubmodules : Fmt := fun
  | `(Lake.«term__.*»| $name:name.*%$globTk) => do
    let name ← fmt name
    let globTk ← fmt globTk
    return Layouts.atomic #[name, globTk]
  | _ => throw .partialFormatter

@[builtin_fmt Lake.«term__.+»]
public def fmtGlobSubmodules : Fmt := fun
  | `(Lake.«term__.+»| $name:name.+%$globTk) => do
    let name ← fmt name
    let globTk ← fmt globTk
    return Layouts.atomic #[name, globTk]
  | _ => throw .partialFormatter
