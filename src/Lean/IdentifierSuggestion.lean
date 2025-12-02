module

prelude
public import Lean.Attributes
public import Lean.Elab.DeclModifiers

namespace Lean

builtin_initialize identifierSuggestionForAttr : ParametricAttribute (Name × Array (Name × Name)) ←
  registerParametricAttribute {
    name := `suggest_for,
    descr := "suggest other (incorrect, not-existing) identifiers that someone might use when they actually want this definition",
    getParam := fun declName stx => do
      let `(attr| suggest_for $[$ids],* ) := stx
        | throwError "Invalid `[suggest_for]` attribute syntax"
      let ns ← getCurrNamespace
      let altNames ← ids.mapM fun id => withRef id do
        Elab.mkDeclName ns {} id.getId
      return (declName, altNames)
    }

public def getSuggestions (fullName : Name) : CoreM (Array Name) :=  do
  let mut possibleReplacements := #[]
  let (_, allSuggestions) := identifierSuggestionForAttr.ext.getState (← getEnv)
  for (_, trueName, suggestions) in allSuggestions do
    for (suggestion, _) in suggestions do
      if fullName = suggestion then
        possibleReplacements := possibleReplacements.push trueName
  return possibleReplacements.qsort (lt := lt)
where
  -- Ensure the result of getSuggestions is stable (if arbitrary)
  lt : Name -> Name -> Bool
    | .anonymous, _ => false
    | .str _ _, .anonymous => true
    | .num _ _, .anonymous => true
    | .str _ _, .num _ _ => true
    | .num _ _, .str _ _ => false
    | .num a n, .num b m => n < m || n == m && lt a b
    | .str a s1, .str b s2 => s1 < s2 || s1 == s2 && lt a b
