import Lean
open Lean Meta Elab Command

/-!
# `withNamespace` should correctly pop scopes after running

Issue: https://github.com/leanprover/lean4/issues/12630

`withNamespace` was not calling `popScopes` on the environment extensions,
causing `scoped syntax` declarations to leak keywords outside their scope.
-/

-- Test 1: `withNamespace` inside namespace shouldn't leak scoped syntax
namespace outer1

#eval do
  withNamespace `inner do
    logInfo "shouldn't affect anything"

scoped syntax "myterm1" : term

end outer1

-- Outside the namespace, `myterm1` should parse as an identifier, not a keyword.
#eval do
  let stx ← `(term|myterm1)
  unless stx.raw.isIdent do
    throwError "expected identifier, got keyword"

-- Test 2: `withNamespace` before namespace shouldn't leak scoped syntax
#eval do
  withNamespace `outer2 do
    logInfo "shouldn't affect anything"

namespace outer2

scoped syntax "myterm2" : term

end outer2

-- Outside the namespace, `myterm2` should parse as an identifier, not a keyword.
#eval do
  let stx ← `(term|myterm2)
  unless stx.raw.isIdent do
    throwError "expected identifier, got keyword"
