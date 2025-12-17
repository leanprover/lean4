/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
module

prelude
public import Lean.ErrorExplanation

/-- -/
register_error_explanation lean.ctorResultingTypeMismatch {
  summary := "Resulting type of constructor was not the inductive type being declared."
  sinceVersion := "4.22.0"
}

/-- -/
register_error_explanation lean.dependsOnNoncomputable {
  summary := "Declaration depends on noncomputable definitions but is not marked as noncomputable"
  sinceVersion := "4.22.0"
}

/-- -/
register_error_explanation lean.inductionWithNoAlts {
  summary := "Induction pattern with nontactic in natural-number-game-style `with` clause."
  sinceVersion := "4.26.0"
}

/-- -/
register_error_explanation lean.inductiveParamMismatch {
  summary := " Invalid parameter in an occurrence of an inductive type in one of its constructors."
  sinceVersion := "4.22.0"
}

/-- -/
register_error_explanation lean.inductiveParamMissing {
  summary := "Parameter not present in an occurrence of an inductive type in one of its constructors."
  sinceVersion := "4.22.0"
}

/-- -/
register_error_explanation lean.inferBinderTypeFailed {
  summary := "The type of a binder could not be inferred."
  sinceVersion := "4.23.0"
}

/-- -/
register_error_explanation lean.inferDefTypeFailed {
  summary := "The type of a definition could not be inferred."
  sinceVersion := "4.23.0"
}

/-- -/
register_error_explanation lean.invalidDottedIdent {
  summary := "Dotted identifier notation used with invalid or non-inferrable expected type."
  sinceVersion := "4.22.0"
}

/-- -/
register_error_explanation lean.invalidField {
  summary := "Generalized field notation used in a potentially ambiguous way."
  sinceVersion := "4.22.0"
}

/-- -/
register_error_explanation lean.projNonPropFromProp {
  summary := "Tried to project data from a proof."
  sinceVersion := "4.23.0"
}

/-- -/
register_error_explanation lean.propRecLargeElim {
  summary := "Attempted to eliminate a proof into a higher type universe."
  sinceVersion := "4.23.0"
}

/-- -/
register_error_explanation lean.redundantMatchAlt {
  summary := "Match alternative will never be reached."
  sinceVersion := "4.22.0"
}

/-- -/
register_error_explanation lean.synthInstanceFailed {
  summary := "Failed to synthesize instance of type class."
  sinceVersion := "4.26.0"
}

/-- -/
register_error_explanation lean.unknownIdentifier {
  summary := "Failed to resolve identifier to variable or constant."
  sinceVersion := "4.23.0"
}
