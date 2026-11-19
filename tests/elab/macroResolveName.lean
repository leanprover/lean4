open Lean in
macro "resolveN" x:ident : term =>
  return quote (k := `term) (← Macro.resolveNamespace x.getId)

open Lean in #check resolveN Macro

open Lean in
macro "resolve" x:ident : term =>
  return quote (k := `term) (← Macro.resolveGlobalName x.getId)

open Nat in #check resolve succ
