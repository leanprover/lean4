-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Floris van Doorn, Jakob von Raumer

prelude
import ..datatypes ..logic
-- Empty type
-- ----------

namespace empty
  protected theorem elim (A : Type) (H : empty) : A :=
  rec (λe, A) H
end empty

protected definition empty.has_decidable_eq [instance] : decidable_eq empty :=
take (a b : empty), decidable.inl (!empty.elim a)
