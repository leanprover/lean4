-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
import logic.eq logic.heq data.unit

structure sigma {A : Type} (B : A → Type) :=
dpair :: (dpr1 : A) (dpr2 : B dpr1)

notation `Σ` binders `,` r:(scoped P, sigma P) := r
