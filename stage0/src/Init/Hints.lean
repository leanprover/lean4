/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.NotationExtra

/- Hint for making sure `Not p` is definitionally equal to `p → False` even when
   `TransparencyMode.reducible` -/
unif_hint (p : Prop) where
  |- Not p =?= p → False
