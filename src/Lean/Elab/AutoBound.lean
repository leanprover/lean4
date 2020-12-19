/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.Options

/- Basic support for auto bound implicit local names -/

namespace Lean.Elab

builtin_initialize
  registerOption `autoBoundImplicitLocal {
    defValue := true
    group    := ""
    descr    := "Unbound local variables in declaration headers become implicit arguments if they are a lower case or greek letter followed by numeric digits. For example, `def f (x : Vector α n) : Vector α n :=` automatically introduces the implicit variables {α n}"
  }

def getAutoBoundImplicitLocalOption (opts : Options) : Bool :=
  opts.get `autoBoundImplicitLocal true

private def allNumeral (s : Substring) : Bool :=
  s.all fun c => c.isDigit || isNumericSubscript c

def isValidAutoBoundImplicitName (n : Name) : Bool :=
  match n.eraseMacroScopes with
  | Name.str Name.anonymous s _ => s.length > 0 && (isGreek s[0] || s[0].isLower) && allNumeral (s.toSubstring.drop 1)
  | _ => false

def isValidAutoBoundLevelName (n : Name) : Bool :=
  match n.eraseMacroScopes with
  | Name.str Name.anonymous s _ => s.length > 0 && s[0].isLower && allNumeral (s.toSubstring.drop 1)
  | _ => false

end Lean.Elab
