import Lean.Environment

open Lean

builtin_initialize valExt : EnvExtension String ←
  registerEnvExtension (pure "Builtin value")
