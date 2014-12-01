-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad

-- tools.helper_tactics
-- ====================

-- Useful tactics.

import logic.eq

open tactic

namespace helper_tactics
  definition apply_refl := apply eq.refl
  tactic_hint apply_refl
end helper_tactics
