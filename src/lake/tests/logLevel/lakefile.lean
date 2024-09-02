import Lake
open Lake DSL

package test

/-
Test logging in Lake CLI
-/

def cfgLogLv? := (get_config? log).bind LogLevel.ofString?

meta if cfgLogLv?.isSome then
  run_cmd Lean.log "bar" cfgLogLv?.get!.toMessageSeverity


/-
Test logging in Lean
-/

lean_lib Log

/-
Test logging in job
-/

def top (level : LogLevel) : FetchM (BuildJob Unit) := Job.async do
  logEntry {level, message := "foo"}
  return ((), .nil)

target topTrace : Unit := top .trace
target topInfo : Unit := top .info
target topWarning : Unit := top .warning
target topError : Unit := top .error

/--
Test logging in build helper
-/

def art (pkg : Package) (level : LogLevel) : FetchM (BuildJob Unit) := Job.async do
  let artFile := pkg.buildDir / s!"art{level.toString.capitalize}"
  (((), ·)) <$> buildFileUnlessUpToDate artFile .nil do
    logEntry {level, message := "foo"}
    createParentDirs artFile
    IO.FS.writeFile artFile ""

target artTrace pkg : Unit := art pkg .trace
target artInfo pkg : Unit := art pkg .info
target artWarning pkg : Unit := art pkg .warning
target artError pkg : Unit := art pkg .error
