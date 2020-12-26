/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Data.Lsp.Basic
import Lean.Data.Json

namespace Lean
namespace Lsp

open Json

structure WorkspaceFolder where
  uri : DocumentUri
  name : String
  deriving ToJson, FromJson

-- TODO(WN):
-- WorkspaceFoldersServerCapabilities,
-- DidChangeWorkspaceFoldersParams,
-- WorkspaceFoldersChangeEvent

end Lsp
end Lean
