import Lean.Util.LeanOptions

/--
Information shared between Lake and Lean when calling `lake setup-file`.
-/
structure Lean.FileSetupInfo where
  paths        : LeanPaths
  setupOptions : LeanOptions
  deriving FromJson, ToJson
