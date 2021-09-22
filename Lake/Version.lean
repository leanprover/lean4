/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.LeanVersion

namespace Lake

def version.major := 2
def version.minor := 1
def version.patch := 0
def version.isPre := false
def versionString := s!"{version.major}.{version.minor}.{version.patch}"
def uiVersionString :=
  s!"Lake version {versionString} (Lean version {uiLeanVersionString})"
