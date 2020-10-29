/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.LeanInit

macro "rfl" : tactic => `(exact rfl)
macro "decide!" : tactic => `(exact decide!)
