import Lean.Data.Lsp.Basic
import Lean.Data.Json

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
