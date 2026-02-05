/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
module

prelude
public import Lean.Data.Lsp.Basic

public section

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

structure RelativePattern where
  baseUri : DocumentUri
  pattern : String
  deriving FromJson, ToJson

inductive GlobPattern where
  | pattern (pat : String)
  | relative (pat : RelativePattern)

instance : FromJson GlobPattern where
  fromJson? j := do
    match j with
    | .str pat => return .pattern pat
    | _ => return .relative <| ← fromJson? j

instance : ToJson GlobPattern where
  toJson
    | .pattern pat => .str pat
    | .relative pat => toJson pat

structure FileSystemWatcher where
  globPattern : GlobPattern
  kind? : Option Nat := none
  deriving FromJson, ToJson

namespace FileSystemWatcher

-- Bit flags for `FileSystemWatcher.kind`
def create := 1
def change := 2
def delete := 4

end FileSystemWatcher

structure DidChangeWatchedFilesRegistrationOptions where
  watchers : Array FileSystemWatcher
  deriving FromJson, ToJson

inductive FileChangeType
  | Created
  | Changed
  | Deleted

instance : FromJson FileChangeType where
  fromJson? j := do
    match (← fromJson? j : Nat) with
      | 1 => return FileChangeType.Created
      | 2 => return FileChangeType.Changed
      | 3 => return FileChangeType.Deleted
      | _ => throw s!"expected 1, 2, or 3, got {j}"

instance : ToJson FileChangeType where
  toJson
    | FileChangeType.Created => toJson 1
    | FileChangeType.Changed => toJson 2
    | FileChangeType.Deleted => toJson 3

structure FileEvent where
  uri : DocumentUri
  type : FileChangeType
  deriving FromJson, ToJson

structure DidChangeWatchedFilesParams where
  changes : Array FileEvent
  deriving FromJson, ToJson

end Lsp
end Lean
