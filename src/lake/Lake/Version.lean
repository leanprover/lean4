/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Prelude
import Init.Data.ToString
import Init.Data.String.TakeDrop

namespace Lake

public def version.major : Nat := 5
public def version.minor : Nat := 0
public def version.patch : Nat := 0

public def version.isRelease : Bool :=
  Lean.version.isRelease

public def version.specialDesc : String :=
  if isRelease && !Lean.githash.isEmpty then s!"src+{Lean.githash.take 7}" else "src"

public def versionStringCore : String :=
  s!"{version.major}.{version.minor}.{version.patch}"

public def versionString : String :=
  if version.specialDesc ≠ "" then
    s!"{versionStringCore}-{version.specialDesc}"
  else
    versionStringCore

public def uiVersionString : String :=
  s!"Lake version {versionString} (Lean version {Lean.versionString})"
