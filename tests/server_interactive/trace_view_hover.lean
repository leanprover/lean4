import Lean
--^ waitForILeans

/-!
Hovers for identifiers in the postprocessor term of `trace_view`: the info trees produced while
elaborating the postprocessor must survive the elaboration of the traced command. Hovers inside
the traced command must also keep working when the postprocessor term fails to elaborate (the
command then falls back to the identity postprocessor).
-/

open scoped Lean.TraceView

set_option trace.Meta.synthInstance true in
trace_view hideSucceeded in
          --^ textDocument/hover
example : Inhabited (List Nat) := inferInstance

set_option trace.Meta.synthInstance true in
trace_view maxDepth 1 >=> grep "result" in
            --^ textDocument/hover
example : Inhabited (List Nat) := inferInstance

set_option trace.Meta.synthInstance true in
trace_view hideSuc in
example : Inhabited (List Nat) := inferInstance
                                --^ textDocument/hover
