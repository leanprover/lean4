/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

namespace Lean

/--
  Create an auxiliary identifier for storing non-atomic discriminants.
  This kind of free variable is cleared before elaborating a `match` alternative rhs.
-/
def mkAuxDiscr [Monad m] [MonadQuotation m] : m Ident :=
  `(_discr)

/--
  Create an auxiliary identifier for expanding notation such as `fun (a, b) => ...`.
  This kind of free variable is cleared before elaborating a `match` alternative rhs.
-/
def mkAuxFunDiscr [Monad m] [MonadQuotation m] : m Ident :=
  `(_fun_discr)

/-- Return true iff `n` is an auxiliary variable created by `expandNonAtomicDiscrs?` -/
def isAuxDiscrName (n : Name) : Bool :=
  n.hasMacroScopes && n.eraseMacroScopes == `_discr

/--
  Return true iff `n` is an auxiliary variable created by notation such as `fun (a, b) => ...`.
  They are cleared before eliminating the `match` alternatives RHS -/
def isAuxFunDiscrName (n : Name) : Bool :=
  n.hasMacroScopes && n.eraseMacroScopes == `_fun_discr

end Lean
