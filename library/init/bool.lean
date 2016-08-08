-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
prelude
import init.datatypes init.reserved_notation

namespace bool
  definition cond [inline] {A : Type} (b : bool) (t e : A) :=
  bool.rec_on b e t

  definition bor [inline] (a b : bool) :=
  bool.rec_on a (bool.rec_on b ff tt) tt

  definition band [inline] (a b : bool) :=
  bool.rec_on a ff (bool.rec_on b ff tt)

  definition bnot [inline] (a : bool) :=
  bool.rec_on a tt ff
end bool

notation a || b := bool.bor a b
notation a && b := bool.band a b
