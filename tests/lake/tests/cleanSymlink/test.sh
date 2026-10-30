#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Regression for #14476: cleaning a symlinked build or cache directory must preserve its target.
if [ "$OS" = Windows_NT ]; then
  exit 0
fi

mkdir -p work
cd work
mkdir -p target/sub
echo 'preserve this file' > target/sub/sentinel

for suffix in '' '/' '///'; do
  cat > lakefile.toml <<EOF
name = "test"
buildDir = "out$suffix"
EOF

  ln -s target out
  test_run clean
  test_exp ! -L out
  test_exp ! -e out
  test_exp -f target/sub/sentinel

  ln -s target cache-link
  LAKE_CACHE_DIR="$PWD/cache-link$suffix" test_run cache clean
  test_exp ! -L cache-link
  test_exp ! -e cache-link
  test_exp -f target/sub/sentinel
done
