/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
prelude
import Lean.Data.JsonRpc

/-! # Defines `Lean.Lsp.CancelParams`.

This is separate from `Lean.Data.Lsp.Basic` to reduce transitive dependencies.
-/

namespace Lean
namespace Lsp

open Json

structure CancelParams where
  id : JsonRpc.RequestID
  deriving Inhabited, BEq, ToJson, FromJson

end Lsp
end Lean
