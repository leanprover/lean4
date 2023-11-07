/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/

namespace Lake

/--
A string descriptor of the `System.Platform` OS
(i.e., `windows`, `macOS`, `emscripten`, or `linux`).
-/
def platformOs : String :=
  if System.Platform.isWindows then
    "windows"
  else if System.Platform.isOSX then
    "macOS"
  else if System.Platform.isEmscripten then
    "emscripten"
  else
    "linux"

/- A string descriptor of the current `System.Platform` -- OS and bit-width. -/
def platformDescriptor :=
  s!"{platformOs}-{System.Platform.numBits}"
