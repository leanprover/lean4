prelude

namespace Lean
class MonadRef where
  getRef : Type
export MonadRef (getRef)
end Lean

open Lean in
#check getRe
          --^ textDocument/completion

namespace Lean
#check getRe
          --^ textDocument/completion
end Lean
