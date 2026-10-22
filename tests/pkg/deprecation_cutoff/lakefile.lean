module

import Lake

/-! A consumer and dependency with independently configurable deprecation cutoffs. -/

open Lake DSL

package cutoff_consumer where
  leanOptions := #[⟨`deprecation.warnings, get_config? cutoff |>.getD "2000-01-01"⟩]

require cutoff_dependency from "dep"

@[default_target] lean_lib Consumer
lean_lib Probe
lean_lib LocalProbe
lean_lib EmptyProbe
