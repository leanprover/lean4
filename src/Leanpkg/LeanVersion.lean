/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich
-/
namespace Leanpkg

def leanVersionStringCore :=
  s!"{Lean.version.major}.{Lean.version.minor}.{Lean.version.patch}"

def origin := "leanprover/lean4"

def leanVersionString :=
  if Lean.version.isRelease then
      s!"{origin}:{leanVersionStringCore}"
  else if Lean.version.specialDesc ≠ "" then
      s!"{origin}:{Lean.version.specialDesc}"
  else
      s!"{origin}:master"

def uiLeanVersionString :=
if Lean.version.isRelease then
    leanVersionStringCore
else if Lean.version.specialDesc ≠ "" then
    Lean.version.specialDesc
else
    s!"master ({leanVersionStringCore})"

end Leanpkg
