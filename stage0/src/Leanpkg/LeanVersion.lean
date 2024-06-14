/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich
-/
namespace Leanpkg

def leanVersionStringCore :=
  s!"{Lean.version.major}.{Lean.version.minor}.{Lean.version.patch}"

def leanVersionString :=
  if Lean.version.isRelease then
      s!"leanprover/lean:{leanVersionStringCore}"
  else if Lean.version.specialDesc ≠ "" then
      Lean.version.specialDesc
  else
      "master"

def uiLeanVersionString :=
if Lean.version.isRelease then
    leanVersionStringCore
else if Lean.version.specialDesc ≠ "" then
    Lean.version.specialDesc
else
    s!"master ({leanVersionStringCore})"

end Leanpkg
