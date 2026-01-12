/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga
-/
module

prelude
public import Lean.Data.Json.Parser
public import Lean.Data.Json.Printer

public section

namespace IO.FS.Stream

open Lean
open IO

def readUTF8 (h : FS.Stream) (nBytes : Nat) : IO String := do
  let bytes ← h.read (USize.ofNat nBytes)
  let some s := String.fromUTF8? bytes | throw (IO.userError "invalid UTF-8")
  return s

/-- Consumes `nBytes` bytes from the stream, interprets the bytes as a utf-8 string and the string as a valid JSON object. -/
def readJson (h : FS.Stream) (nBytes : Nat) : IO Json := do
  let bytes ← h.read (USize.ofNat nBytes)
  let some s := String.fromUTF8? bytes | throw (IO.userError "invalid UTF-8")
  ofExcept (Json.parse s)

def writeJson (h : FS.Stream) (j : Json) : IO Unit := do
  h.putStr j.compress
  h.flush

end IO.FS.Stream
