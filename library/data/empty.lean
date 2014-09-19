-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Floris van Doorn

-- Empty type
-- ----------

import logic.core.cast

inductive empty : Type

namespace empty
  protected theorem elim (A : Type) (H : empty) : A :=
  rec (λe, A) H
end empty

namespace false
  theorem to_empty (H : false) : empty :=
  cast (false_elim H) true

  theorem rec_type (A : Type) (H : false) : A :=
  empty.rec (λx,A) (to_empty H)
end false
