module

meta import Lean.PostprocessTraces
--^ waitForILeans

/-!
Hovers for identifiers in the postprocessor term of `postprocess_traces`: the info trees produced while
elaborating the postprocessor must survive the elaboration of the traced command. Hovers inside
the traced command must also keep working when the postprocessor term fails to elaborate (the
command then falls back to the identity postprocessor).
-/

open scoped Lean.PostprocessTraces

set_option trace.Meta.synthInstance true in
postprocess_traces countNodes in
                      --^ textDocument/hover
example : Inhabited (List Nat) := inferInstance

set_option trace.Meta.synthInstance true in
postprocess_traces filterSubtrees (containsString "result") in
                      --^ textDocument/hover
example : Inhabited (List Nat) := inferInstance
