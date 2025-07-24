/-
Copyright (c) 2021 Joscha Mennicken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Joscha Mennicken
-/
prelude
import Lean.Data.Lsp.Basic

namespace Lean
namespace Lsp

open Json

structure Registration where
  id : String
  method : String
  registerOptions : Option Json
  deriving ToJson, FromJson

structure RegistrationParams where
  registrations : Array Registration
  deriving ToJson, FromJson

end Lsp
end Lean
