prelude

namespace Lean
class MonadRef where
  getRef : Type
export MonadRef (getRef)
end Lean

open Lean in
#check getRe
          --^ completion

namespace Lean
#check getRe
          --^ completion
end Lean
