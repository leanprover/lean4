/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import leanpkg.config_vars

namespace leanpkg

open lean_version

def lean_version_string_core :=
major.repr ++ "." ++ minor.repr ++ "." ++ patch.repr

def lean_version_string :=
if is_release then
    lean_version_string_core
else
    "master"

def ui_lean_version_string :=
if is_release then
    lean_version_string_core
else
    "master (" ++ lean_version_string_core ++ ")"

end leanpkg