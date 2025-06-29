import Lean.ErrorExplanation
import Lean.Exception
import Lean.Log

/-!
# Error explanation interactive tests

Tests completions and hovers for error explanations.
-/

/-- Example -/
register_error_explanation testPkg.bar {
  summary := "Error 0"
  sinceVersion := "4.0.0"
}

/-- Example -/
register_error_explanation testPkg.foo1 {
  summary := "Error 1"
  sinceVersion := "4.0.0"
}

/-- Example -/
register_error_explanation testPkg.foo2 {
  summary := "Error 2"
  sinceVersion := "4.0.0"
}

#check throwNamedError testPkg
                            --^ textDocument/completion
#check throwNamedError testPkg.
                             --^ textDocument/completion
#check throwNamedError testPkg.f
                              --^ textDocument/completion
#check throwNamedError testPkg.f "test"
                              --^ textDocument/completion

#check throwNamedError testPkg.foo2
                             --^ textDocument/hover
#check throwNamedError testPkg.foo2 "test"
                             --^ textDocument/hover
