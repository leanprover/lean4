import .tactic
open tactic

namespace fake_simplifier

-- until we have the simplifier...
opaque definition simp : tactic := apply @sorry

end fake_simplifier
