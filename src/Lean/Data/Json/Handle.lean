/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga
-/
import Init.System.IO
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import Lean.Data.Json.FromToJson

namespace IO.FS.Handle

open Lean
open IO

def readJson (h : FS.Handle) (nBytes : Nat) : IO Json := do
bytes ← h.read nBytes;
some s ← pure bytes.utf8ToString
  | throw (userError ("got non-utf8 string '" ++ toString bytes ++ "'"));
ofExcept (Json.parse s)

def writeJson (h : FS.Handle) (j : Json) : IO Unit := do
h.putStr j.compress;
h.flush

end IO.FS.Handle
