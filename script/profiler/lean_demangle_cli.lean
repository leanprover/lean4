/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import Lean.Compiler.NameDemangling

/-!
Lean name demangler CLI tool. Reads mangled symbol names from stdin (one per
line) and writes demangled names to stdout. Non-Lean symbols pass through
unchanged. Like `c++filt` but for Lean names.

Usage:
    echo "l_Lean_Meta_foo" | lean --run lean_demangle_cli.lean
    cat symbols.txt | lean --run lean_demangle_cli.lean
-/

open Lean.Name.Demangle

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat do
    let line ← stdin.getLine
    if line.isEmpty then break
    let sym := line.trimRight
    match demangleSymbol sym with
    | some s => stdout.putStrLn s
    | none => stdout.putStrLn sym
    stdout.flush
