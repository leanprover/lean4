/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.Data.ToString

namespace Lake

def version.major := 5
def version.minor := 0
def version.patch := 0

def version.isRelease :=
  Lean.version.isRelease

def version.specialDesc :=
  if isRelease && !Lean.githash.isEmpty then Lean.githash.take 7 else "src"

def versionStringCore :=
  s!"{version.major}.{version.minor}.{version.patch}"

def versionString :=
  if version.specialDesc ≠ "" then
    s!"{versionStringCore}-{version.specialDesc}"
  else
    versionStringCore

def uiVersionString :=
  s!"Lake version {versionString} (Lean version {Lean.versionString})"
