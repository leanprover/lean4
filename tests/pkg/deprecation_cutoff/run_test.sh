capture lake -R build Consumer

capture lake -R build Probe
if grep -Fq 'has been deprecated' "$CAPTURED.out.produced"; then
  fail "dependency warnings should be delayed"
fi

# Changing the package option must rebuild Probe without clearing its artifacts.
capture lake -R -Kcutoff=2000-01-02 build Probe
check_out_contains 'old dependency module'
check_out_contains 'old dependency name'

capture lake -R -Kcutoff=2000-01-01 build Probe
if grep -Fq 'has been deprecated' "$CAPTURED.out.produced"; then
  fail "moving the cutoff back should suppress dependency warnings"
fi

capture lake -R -Kcutoff=all build LocalProbe
check_out_contains 'old local module'
if grep -Fq 'old dependency module' "$CAPTURED.out.produced"; then
  fail "deprecated_module: ignore should still suppress an enabled warning"
fi

capture_fail lake -R -Kcutoff=2023-02-29 build EmptyProbe
check_out_contains 'Invalid value for `deprecation.warnings`'

capture_fail lean -Ddeprecation.warnings=2023-02-29 EmptyProbe.lean
check_out_contains 'Invalid value for `deprecation.warnings`'

capture lean -Ddeprecation.warnings=2024-02-29 EmptyProbe.lean
