-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad
import data.unit.decl logic.eq

structure prod (A B : Type) :=
mk :: (pr1 : A) (pr2 : B)

definition pair := @prod.mk

namespace prod
  notation A × B := prod A B
  notation `pr₁` := pr1
  notation `pr₂` := pr2

  -- notation for n-ary tuples
  notation `(` h `,` t:(foldl `,` (e r, prod.mk r e) h) `)` := t
end  prod
