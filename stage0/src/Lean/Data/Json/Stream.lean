/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga
-/
import Init.System.IO
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import Lean.Data.Json.FromToJson

namespace IO.FS.Stream

open Lean
open IO

/-- Consumes `nBytes` bytes from the stream, interprets the bytes as a utf-8 string and the string as a valid JSON object. -/
def readJson (h : FS.Stream) (nBytes : Nat) : IO Json := do
  let bytes ← h.read (USize.ofNat nBytes)
  let s := String.fromUTF8Unchecked bytes
  ofExcept (Json.parse s)

def writeJson (h : FS.Stream) (j : Json) : IO Unit := do
  h.putStr j.compress
  h.flush

end IO.FS.Stream
