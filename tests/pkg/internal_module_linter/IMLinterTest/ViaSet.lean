/-!
Tests that the `internalModule` linter can be enabled via the `linter.coreInternal` linter set:
this module is built with only `linter.coreInternal = true` (see the `SetMain` library in the
lakefile), without setting `linter.coreInternal.internalModule` itself.
-/

-- warns: the linter is enabled through the `linter.coreInternal` set
def viaSetLeaky := 9

-- no warning: explicitly disabling the linter takes precedence over the enabled set
set_option linter.coreInternal.internalModule false in
def viaSetDisabled := 10
