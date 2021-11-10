/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich
-/
namespace Lake

def leanVersionStringCore :=
  s!"{Lean.version.major}.{Lean.version.minor}.{Lean.version.patch}"

def leanOrigin := "leanprover/lean4"

def leanVersionString :=
  if Lean.version.isRelease then
    s!"{leanOrigin}:{leanVersionStringCore}"
  else if Lean.version.specialDesc ≠ "" then
    s!"{leanOrigin}:{Lean.version.specialDesc}"
  else
    s!"{leanOrigin}:master"

def uiLeanVersionString :=
if Lean.version.isRelease then
  leanVersionStringCore
else if Lean.version.specialDesc ≠ "" then
  s!"{leanVersionStringCore}-{Lean.version.specialDesc}"
else
  s!"master ({leanVersionStringCore})"
