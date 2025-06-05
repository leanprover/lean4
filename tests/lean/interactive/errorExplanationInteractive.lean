import Lean.ErrorExplanation

/-!
# Error explanation interactive tests

Tests completions and hovers for error explanations.
-/

/-- Example -/
register_error_explanation Lean.Bar {
  summary := "Error 0"
  sinceVersion := "4.0.0"
}

/-- Example -/
register_error_explanation Lean.Foo1 {
  summary := "Error 1"
  sinceVersion := "4.0.0"
}

/-- Example -/
register_error_explanation Lean.Foo2 {
  summary := "Error 2"
  sinceVersion := "4.0.0"
}

#check throwNamedError Lean
                         --^ textDocument/completion
#check throwNamedError Lean.
                          --^ textDocument/completion
#check throwNamedError Lean.F
                           --^ textDocument/completion
#check throwNamedError Lean.F "test"
                           --^ textDocument/completion

#check throwNamedError Lean.Foo2
                          --^ textDocument/hover
#check throwNamedError Lean.Foo2 "test"
                          --^ textDocument/hover
