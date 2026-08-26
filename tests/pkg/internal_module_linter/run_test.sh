rm -rf .lake

# Build all test modules; the `Main` lib enables `linter.coreInternal.internalModule` directly via
# `leanOptions` in the lakefile, the `SetMain` lib enables only the `linter.coreInternal` set.
capture lake build Main SetMain

# `IMLinterTest` is an internal module via a test-only entry in `internalModulePrefixes`.
check_out_contains '`leaky` is a non-internal declaration in the internal module `IMLinterTest`'

# "Internal" as a mere substring of a declaration-name component does not make it internal.
check_out_contains '`myInternalHelper` is a non-internal declaration in the internal module `IMLinterTest`'

# Submodules of an `internalModulePrefixes` entry are internal, too.
check_out_contains '`subLeaky` is a non-internal declaration in the internal module `IMLinterTest.Sub`'

# `Helpers.Internal` is an internal module via its `Internal` name component.
check_out_contains '`helpersLeaky` is a non-internal declaration in the internal module `Helpers.Internal`'

# The linter also fires when enabled via the `linter.coreInternal` set instead of directly.
check_out_contains '`viaSetLeaky` is a non-internal declaration in the internal module `IMLinterTest.ViaSet`'

# Internal declarations (private, `Lean` namespace, `Internal` name component) must not be
# flagged, and neither must declarations in non-internal modules: `UsesInternalHelpers` only
# contains "Internal" as a substring of a component, and `Regular` does not match at all.
# `viaSetDisabled` sets `linter.coreInternal.internalModule false` locally, which overrides the enabled set.
for decl in privateHelper pkgTestHelper Internal.helper Impl.Internal.deepHelper substringLeaky regularDef viaSetDisabled; do
  if grep -Fq "\`$decl\`" "$CAPTURED.out.produced"; then
    fail "$decl should not trigger the internalModule linter"
  fi
done
