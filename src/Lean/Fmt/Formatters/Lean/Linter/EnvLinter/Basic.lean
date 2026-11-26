/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Linter.EnvLinter.Basic
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Linter.EnvLinter.builtin_env_linter]
public def fmtBuiltinEnvLinter : Fmt := fun
  | `(Lean.Linter.EnvLinter.builtin_env_linter| builtin_env_linter%$linterTk $optionId:ident) => do
    let linterTk ← fmt linterTk
    let optionId ← fmt optionId
    return Layouts.pseudoApplication #[linterTk, optionId]
  | _ => throw .partialFormatter
