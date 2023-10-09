/-
Copyright (c) 2023 Lean FRO, LLC.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.Data.JsonRpc

namespace Lean.Lsp

/-- The `PositionEncodingKind` enum that was added in LSP 3.17 so
clients can advertise encoding support -/
inductive PositionEncodingKind where
  | utf8 | utf16 | utf32
deriving BEq, Repr

instance : ToJson PositionEncodingKind where
  toJson
    | .utf8 => "utf-8"
    | .utf16 => "utf-16"
    | .utf32 => "utf-32"

instance : FromJson PositionEncodingKind where
  fromJson?
    | .str "utf-8" => pure .utf8
    | .str "utf-16" => pure .utf16
    | .str "utf-32" => pure .utf32
    | _ => throw "expected \"utf-8\", \"utf-16\", or \"utf-32\""
