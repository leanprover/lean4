import Lean

set_option linter.suspiciousUnexpanderPatterns true

@[appUnexpander List.nil] def unexpandListNilBad : Lean.PrettyPrinter.Unexpander
  | `(List.nil) => `([])
  | _       => throw ()

/--hey-/
@[appUnexpander List.cons] private def unexpandListConsBad : Lean.PrettyPrinter.Unexpander
  | `(List.cons $x [])      => `([$x])
  | _                       => throw ()
