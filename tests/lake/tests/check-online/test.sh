#!/usr/bin/env bash
source ../common.sh

./clean.sh

init_check_sandbox

# Dependency resolution is the one step that the sandbox gives network access to. Starting from a
# manifest but no packages, it has to fetch the dependency over HTTPS from inside the sandbox.
check_fetches() {
  rm -rf .lake
  test_cmd git --version
  test_status_out 0 'Lean default kernel accepts the solution' check
  test_exp -d .lake/packages/Cli/.git
}

test_run update --keep-toolchain
check_fetches

if [ "$UNAME" = Darwin ]; then
  # The `git` that macOS provides, which checks certificates through system services.
  PATH="/usr/bin:$PATH" check_fetches
fi

rm -f produced.out
