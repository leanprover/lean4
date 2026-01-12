/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
module

prelude

public import Lean.Message
public import Lean.EnvExtension
public import Lean.DocString.Links
import Init.Data.String.TakeDrop
import Init.Data.String.Extra
import Init.Data.String.Search

public section

namespace Lean

/--
Metadata for an error explanation.

* `summary` gives a short description of the error
* `sinceVersion` indicates the version of Lean in which an error with this error name was introduced
* `severity` is the severity of the diagnostic
* `removedVersion` indicates the version of Lean in which this error name was retired, if applicable
-/
structure ErrorExplanation.Metadata where
  summary : String
  sinceVersion : String
  severity : MessageSeverity     := .error
  removedVersion? : Option String := none
  deriving FromJson, ToJson

/--
An explanation of a named error message.

Error explanations are rendered in the manual; a link to the resulting manual page is displayed at
the bottom of corresponding error messages thrown using `throwNamedError` or `throwNamedErrorAt`.
-/
structure ErrorExplanation where
  /-- The `doc` field is deprecated and should always be the empty string -/
  doc : String
  metadata : ErrorExplanation.Metadata
  declLoc? : Option DeclarationLocation

/--
Returns the error explanation summary prepended with its severity. For use in completions and
hovers.
-/
def ErrorExplanation.summaryWithSeverity (explan : ErrorExplanation) : String :=
  s!"({explan.metadata.severity}) {explan.metadata.summary}"

/-- An environment extension that stores error explanations.  -/
builtin_initialize errorExplanationExt : SimplePersistentEnvExtension (Name × ErrorExplanation) (NameMap ErrorExplanation) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s (n, v) => s.insert n v
    addImportedFn := fun ess =>
      ess.foldl (init := ∅) fun acc es =>
        es.foldl (init := acc) fun acc (n, v) =>
          acc.insert n v
  }

/-- Returns an error explanation for the given name if one exists. -/
def getErrorExplanation? [Monad m] [MonadEnv m] (name : Name) : m (Option ErrorExplanation) := do
  return errorExplanationExt.getState (← getEnv) |>.find? name

@[deprecated getErrorExplanation? (since := "2026-12-20")]
def getErrorExplanationRaw? (env : Environment) (name : Name) : Option ErrorExplanation := do
  errorExplanationExt.getState env |>.find? name

/-- Returns `true` if there exists an error explanation named `name`. -/
def hasErrorExplanation [Monad m] [MonadEnv m] (name : Name) : m Bool :=
  return errorExplanationExt.getState (← getEnv) |>.contains name

/-- Returns all error explanations with their names, sorted by name. -/
public def getErrorExplanations [Monad m] [MonadEnv m] : m (Array (Name × ErrorExplanation)) := do
  return errorExplanationExt.getState (← getEnv)
    |>.toArray
    |>.qsort fun e e' => e.1.toString < e'.1.toString

@[deprecated getErrorExplanations (since := "2026-12-20")]
public def getErrorExplanationsRaw (env : Environment) : Array (Name × ErrorExplanation) :=
  errorExplanationExt.getState env
    |>.toArray
    |>.qsort fun e e' => e.1.toString < e'.1.toString

@[deprecated getErrorExplanations (since := "2026-12-20")]
public def getErrorExplanationsSorted [Monad m] [MonadEnv m] : m (Array (Name × ErrorExplanation)) := do
  getErrorExplanations

end Lean

/-
Error explanations registered in the compiler must be added to the manual and
referenced in the Manual.ErrorExplanations module here:

https://github.com/leanprover/reference-manual/blob/main/Manual/ErrorExplanations.lean

Details:
https://github.com/leanprover/reference-manual/blob/main/Manual/ErrorExplanations/README.md
-/

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
