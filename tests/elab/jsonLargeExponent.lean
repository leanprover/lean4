import Lean.Data.Json

#guard match Lean.Json.parse "3E9999999993" with
  | .error _ => true
  | .ok _ => false
