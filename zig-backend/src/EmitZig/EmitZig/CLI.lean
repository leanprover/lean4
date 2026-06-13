/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Factory
-/
module

import EmitZig
import Lean.Elab.Frontend
public import Lean.Expr
public import Lean.Compiler.LCNF.Basic
import Lean.Util.Path

open Lean Compiler LCNF

namespace EmitZig

private def nthParent (p : System.FilePath) : Nat → Option System.FilePath
  | 0 => some p
  | n + 1 => p.parent.bind (nthParent · n)

/-- The zig-backend checkout containing this package, derived from the
executable location (`<zig-backend>/src/EmitZig/.lake/build/bin/<exe>`). -/
public def zigBackendDir : IO System.FilePath := do
  let exe ← IO.appPath
  let some dir := nthParent exe 6
    | throw <| IO.userError s!"cannot locate the zig-backend root from {exe}"
  return dir

/-- The lean4 repository root: `$LEAN4_DIR` if set, otherwise the parent of
the zig-backend checkout. -/
public def lean4Dir : IO System.FilePath := do
  if let some dir ← IO.getEnv "LEAN4_DIR" then
    return dir
  let some dir := (← zigBackendDir).parent
    | throw <| IO.userError "cannot derive the lean4 root; set LEAN4_DIR"
  return dir

public def stage1Sysroot : IO System.FilePath :=
  return (← lean4Dir) / "build" / "release" / "stage1"

public def stage1Lean : IO System.FilePath :=
  return (← stage1Sysroot) / "bin" / "lean"

def packageLeanPath : IO System.FilePath :=
  return (← zigBackendDir) / "src" / "EmitZig" / ".lake" / "build" / "lib" / "lean"
public def usageLine := "usage: emitzig <input.lean> -o <output.zig>"

private def shouldShowHelp (args : List String) : Bool := args == ["--help"] || args == ["-h"]
private def parseArgs : List String → Except String (System.FilePath × System.FilePath)
  | [input, "-o", output] => .ok (input, output)
  | _ => .error usageLine
private def quoteLeanString (s : String) := "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

public unsafe def emitFile (input output : System.FilePath) : IO Unit := do
  let sysroot ← Lean.findSysroot (← stage1Lean).toString; Lean.initSearchPath sysroot; Lean.enableInitializersExecution
  let contents ← IO.FS.readFile input
  let modName ← moduleNameOfFileName input input.parent
  let some env ← Lean.Elab.runFrontend contents {} input.toString modName | throw <| IO.userError s!"failed to elaborate '{input}'"
  let zig ← EmitZig.emitZig modName |>.toIO' { fileName := input.toString, fileMap := default } { env }
  IO.FS.writeFile output zig

public unsafe def emitzigMain (args : List String) : IO UInt32 := do
  if shouldShowHelp args then IO.println usageLine; return 0
  match parseArgs args with
  | .error msg => IO.eprintln msg; return 1
  | .ok (input, output) =>
    try
      let scratch ← IO.FS.createTempDir
      let script := scratch / "EmitZigDriver.lean"
      IO.FS.writeFile script <| String.intercalate "\n" [
        "import EmitZig.CLI", "#eval do",
        s!"  let input : System.FilePath := {quoteLeanString input.toString}",
        s!"  let output : System.FilePath := {quoteLeanString output.toString}",
        "  EmitZig.emitFile input output"
      ]
      let out ← IO.Process.output { cmd := (← stage1Lean).toString, args := #[script.toString], env := #[("LEAN_SYSROOT", (← stage1Sysroot).toString), ("LEAN_PATH", (← packageLeanPath).toString)] }
      unless out.exitCode == 0 do IO.eprintln <| if out.stderr.isEmpty then out.stdout else out.stderr; return 1
      return 0
    catch err => IO.eprintln s!"emitzig: {err}"; return 1

public unsafe def main : List String → IO UInt32 := emitzigMain

end EmitZig
