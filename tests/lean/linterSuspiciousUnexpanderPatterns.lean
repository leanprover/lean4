import Lean

set_option linter.suspiciousUnexpanderPatterns true

@[app_unexpander List.nil] def unexpandListNilBad : Lean.PrettyPrinter.Unexpander
  | `(List.nil) => `([])
  | _       => throw ()

/--hey-/
@[app_unexpander List.cons] private def unexpandListConsBad : Lean.PrettyPrinter.Unexpander
  | `(List.cons $x [])      => `([$x])
  | _                       => throw ()
