/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.LeanInit
import Init.System.IO
import Init.Data.ToString
new_frontend

macro "println!" x:(interpolatedStr term) : term => `(IO.println (s! $x))
