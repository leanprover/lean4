# Checks which native function symbols the generated C code exports.

BASIC=.lake/build/ir/ExportSymbols/Basic.c
REUSE=.lake/build/ir/ExportSymbols/Reuse.c

# Succeeds iff the given function is declared in the given file with/without `LEAN_EXPORT`.
function exported {
  grep -Eq "^LEAN_EXPORT lean_object\* [A-Za-z0-9_]*$2\(" "$1"
}
function not_exported {
  grep -Eq "^lean_object\* [A-Za-z0-9_]*$2\(" "$1" && ! exported "$1" "$2"
}

rm -rf .lake
lake build

# Public, `meta`, and `@[export]` functions are exported, each together with its boxed variant.
for fn in publicFn publicFn___boxed metaFn metaFn___boxed export_symbols_exported exportedFn___boxed; do
  exported $BASIC $fn || fail "Expected '$fn' to be exported"
done

# All other functions, including specializations, are not.
for fn in privateFn moduleLocalFn specializingFn specializingFn_spec__0; do
  not_exported $BASIC $fn || fail "Expected '$fn' not to be exported"
  not_exported $BASIC ${fn}___boxed || fail "Expected '${fn}___boxed' not to be exported"
done

# As the specialization in `Basic` is not exported, `Reuse` must not refer to it despite having
# access to the specialization cache of `Basic` via `import all`.
not_exported $REUSE reusingFn_spec__0 || fail "Expected 'Reuse' to create its own specialization"
if grep -q specializingFn $REUSE; then
  fail "Expected 'Reuse' not to refer to the specialization in 'Basic'"
fi
