open Lean in
macro "resolveN" x:ident : term =>
  return quote (← Macro.resolveNamespace? x.getId)

open Lean in #check resolveN Macro

open Lean in
macro "resolve" x:ident : term =>
  return quote (← Macro.resolveGlobalName x.getId)

open Nat in #check resolve succ
