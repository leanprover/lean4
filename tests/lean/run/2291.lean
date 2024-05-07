/-!
Issue #2291

The following example would cause the pretty printer to panic.
-/

set_option trace.compiler.simp true in
#eval [0]
