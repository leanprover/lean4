/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.num init.relation

definition pair [constructor] := @prod.mk
notation A × B := prod A B
-- notation for n-ary tuples
notation `(` h `, ` t:(foldl `, ` (e r, prod.mk r e) h) `)` := t

namespace prod
  notation `pr₁` := pr1
  notation `pr₂` := pr2

  namespace ops
  postfix `.1`:(max+1) := pr1
  postfix `.2`:(max+1) := pr2
  end ops

end prod
