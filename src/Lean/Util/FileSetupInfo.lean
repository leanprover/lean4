import Lean.Util.ServerOptions

/--
Information shared between Lake and Lean when calling `lake setup-file`.
-/
structure Lean.FileSetupInfo where
  paths        : LeanPaths
  setupOptions : ServerOptions
  deriving FromJson, ToJson
