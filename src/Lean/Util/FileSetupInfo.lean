/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
import Lean.Util.LeanOptions

/--
Information shared between Lake and Lean when calling `lake setup-file`.
-/
structure Lean.FileSetupInfo where
  paths        : LeanPaths
  setupOptions : LeanOptions
  deriving FromJson, ToJson
