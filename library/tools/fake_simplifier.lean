import .tactic
open tactic

namespace fake_simplifier

-- until we have the simplifier...
definition simp [opaque] : tactic := apply @sorry

end fake_simplifier
