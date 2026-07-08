import Lean.Meta.Basic

open Lean.Meta

def traceIt : MetaM Unit := do
  Lean.withTraceNode `Meta.debug (fun _ => return m!"root") do
    Lean.withTraceNode `Meta.debug (fun _ => return m!"child1") do
      trace[Meta.debug] "child11"
      trace[Meta.debug] "child12"
      trace[Meta.debug] "child13"
    Lean.withTraceNode `Meta.debug (fun _ => return m!"child2") do
      trace[Meta.debug] "child21"
      trace[Meta.debug] "child22"
    Lean.withTraceNode `Meta.debug (fun _ => return m!"child3") do
      trace[Meta.debug] "child31"
    trace[Meta.debug] "child4"

set_option trace.Meta.debug true

#eval traceIt

--^ collectDiagnostics
--^ interactiveDiagnostics:expandTraces
