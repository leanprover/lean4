/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
prelude
import Lean.Util.LeanOptions

set_option linter.deprecated false in
/--
Information shared between Lake and Lean when calling `lake setup-file`.
-/
@[deprecated "Deprecated without replacement." (since := "2025-06-29")]
structure Lean.FileSetupInfo where
  paths        : LeanPaths
  setupOptions : LeanOptions
  deriving FromJson, ToJson
