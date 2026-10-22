module

import Dependency.Old

/-! Import and declaration warnings respond to package-wide configuration changes. -/

set_option linter.deprecated true

example : Nat := Dep.old
