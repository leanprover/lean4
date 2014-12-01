-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic.eq

namespace unit
  protected theorem equal (a b : unit) : a = b :=
  rec_on a (rec_on b rfl)

  theorem eq_star (a : unit) : a = star :=
  equal a star
end unit
