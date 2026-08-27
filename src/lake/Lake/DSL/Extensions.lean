/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Environment

open Lean

namespace Lake

public builtin_initialize nameExt : EnvExtension (Nat × Name) ←
  registerEnvExtension (pure ⟨0, .anonymous⟩)

public builtin_initialize dirExt : EnvExtension (Option System.FilePath) ←
  registerEnvExtension (pure none)

public builtin_initialize optsExt : EnvExtension (Option (NameMap String)) ←
  registerEnvExtension (pure none)
