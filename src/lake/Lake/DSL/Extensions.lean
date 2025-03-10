/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Environment

open Lean

namespace Lake

initialize dirExt : EnvExtension (Option System.FilePath) ←
  registerEnvExtension (pure none)

initialize optsExt : EnvExtension (Option (NameMap String)) ←
  registerEnvExtension (pure none)
