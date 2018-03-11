/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
namespace leanpkg

def lean_version_string_core :=
let (major, minor, patch) := lean.version in
sformat!("{major}.{minor}.{patch}")

def lean_version_string :=
if lean.is_release then
    lean_version_string_core
else if lean.special_version_desc ≠ "" then
    lean.special_version_desc
else
    "master"

def ui_lean_version_string :=
if lean.is_release then
    lean_version_string_core
else if lean.special_version_desc ≠ "" then
    lean.special_version_desc
else
    "master (" ++ lean_version_string_core ++ ")"

end leanpkg
