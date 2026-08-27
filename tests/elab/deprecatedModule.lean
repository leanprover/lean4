module

import Std.Data


deprecated_module (since := "30-03-2026")

/--
info: Deprecated modules

'elab.deprecatedModule' deprecates to
#[Std.Data]
with no message
-/
#guard_msgs in
#show_deprecated_modules

/-- warning: module is already marked as deprecated -/
#guard_msgs in
deprecated_module "custom message" (since := "30-03-2026")

/--
info: Deprecated modules

'elab.deprecatedModule' deprecates to
#[Std.Data]
with message 'custom message'
-/
#guard_msgs in
#show_deprecated_modules
