-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Floris van Doorn

-- Empty type
-- ----------

import logic.cast

inductive empty : Type

namespace empty
  protected theorem elim (A : Type) (H : empty) : A :=
  rec (λe, A) H

  protected theorem subsingleton [instance] : subsingleton empty :=
  subsingleton.intro (λ a b, !elim a)
end empty
