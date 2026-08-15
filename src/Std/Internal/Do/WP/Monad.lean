/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.WP.Monad.Basic
public import Std.Internal.Do.WP.Monad.Instances
public import Std.Internal.Do.WP.Monad.Adequacy
public import Std.Internal.Do.WP.Monad.Conjunctive
public import Std.Internal.Do.WP.Monad.Frame
public import Std.Internal.Do.WP.Monad.Lemmas

set_option linter.missingDocs true

/-!
# The weakest precondition interpretation of a monad

`Std.Internal.Do.WP` is generic over the program type. The modules gathered here interpret a monad
and the monad transformers, so every declaration below mentions a monad.
-/
