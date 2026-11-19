# These proofs take a while to check, so they only run in CI unless requested.
if [[ -z "$CI" && -z "$LEAN_TEST_VERIF" ]]; then
  echo "Skipped, set LEAN_TEST_VERIF=1 to run"
  exit 77
fi

rm -rf .lake
lake build --wfail
