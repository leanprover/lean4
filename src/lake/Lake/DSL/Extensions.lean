/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Environment

open Lean

namespace Lake

builtin_initialize dirExt : EnvExtension (Option System.FilePath) ←
  registerEnvExtension (pure none)

builtin_initialize optsExt : EnvExtension (Option (NameMap String)) ←
  registerEnvExtension (pure none)
