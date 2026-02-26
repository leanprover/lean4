module

import Init.Control.Do
import Lean.Data.Json

set_option linter.unusedVariables true
set_option backward.do.legacy false

-- Regression tests: variables used in non-atomic match discriminants in `do`
-- should not trigger unused variable warnings.

open Lean in
def test1 (s? : Option String) : IO (Option Nat) := do
  let r ← s?.mapM fun s => do
    let s ← pure (s ++ "")
    match Json.parse s >>= fromJson? with
    | .ok v => pure v
    | .error e => throw <| IO.userError s!"bad: {e}"
  return r

open Lean in
def test2 (s? : Option String) : IO (Option Nat) := do
  let r ← s?.mapM fun s => do
    let s ← pure (s ++ "")
    match Json.parse s >>= fromJson? with
    | .ok v => pure v
    | .error _ => pure 0
  return r

open Lean in
def test3 (env : IO (Option String)) : IO (Option Nat) := do
  let some urlMapStr ← env | return none
  match Json.parse urlMapStr >>= fromJson? with
  | .ok urlMap => return urlMap
  | .error e => throw <| IO.userError s!"invalid JSON: {e}"

open Lean in
def test4 (header? : Option String) : IO (Option Nat) := do
  let header ← header?.mapM fun header => do
    let header ← if header == "" then pure "default" else pure header
    match Json.parse header >>= fromJson? with
    | .ok header => pure header
    | .error e => throw <| IO.userError s!"failed to parse: {e}"
  return header
