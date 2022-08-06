/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake

def version.major := 4
def version.minor := 0
def version.patch := 0

def version.isPrerelease := false
def version.isRelease := !isPrerelease
def version.specialDesc := if isPrerelease then "pre" else ""

def versionStringCore :=
  s!"{version.major}.{version.minor}.{version.patch}"

def versionString :=
  if version.specialDesc ≠ "" then
    s!"{versionStringCore}-{version.specialDesc}"
  else
    versionStringCore

def uiVersionString :=
  s!"Lake version {versionString} (Lean version {Lean.versionString})"
