-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

import algebra.category

open eq eq.ops category

namespace morphism
  section
  parameter {ob : Type}
  parameter {C : category ob}
  variables {a b c d : ob} {h : mor c d} {g : mor b c} {f : mor a b}
  end
end morphism
