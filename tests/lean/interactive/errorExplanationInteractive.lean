import Lean.ErrorExplanation
import Lean.Exception
import Lean.Log

/-!
# Error explanation interactive tests

Tests completions and hovers for error explanations.
-/

/-- Example -/
register_error_explanation TestDomain.Bar {
  summary := "Error 0"
  sinceVersion := "4.0.0"
}

/-- Example -/
register_error_explanation TestDomain.Foo1 {
  summary := "Error 1"
  sinceVersion := "4.0.0"
}

/-- Example -/
register_error_explanation TestDomain.Foo2 {
  summary := "Error 2"
  sinceVersion := "4.0.0"
}

#check throwNamedError TestDomain
                               --^ textDocument/completion
#check throwNamedError TestDomain.
                                --^ textDocument/completion
#check throwNamedError TestDomain.F
                                 --^ textDocument/completion
#check throwNamedError TestDomain.F "test"
                                 --^ textDocument/completion

#check throwNamedError TestDomain.Foo2
                                --^ textDocument/hover
#check throwNamedError TestDomain.Foo2 "test"
                                --^ textDocument/hover
