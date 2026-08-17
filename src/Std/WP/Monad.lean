/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.WP.Monad.Basic
public import Std.WP.Monad.Instances
public import Std.WP.Monad.Adequacy
public import Std.WP.Monad.Conjunctive
public import Std.WP.Monad.Frame
public import Std.WP.Monad.Lemmas

set_option linter.missingDocs true

/-!
# The weakest precondition interpretation of a monad

`Std.WP.Basic` is generic over the program type. The modules gathered here interpret a monad
and the monad transformers, so every declaration below mentions a monad.
-/
