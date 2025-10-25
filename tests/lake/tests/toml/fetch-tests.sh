#!/usr/bin/env bash
set -euo pipefail

git clone https://github.com/toml-lang/toml-test toml-test --depth 1 --branch v1.4.0
TOML_VER=${1:-1.0.0}
echo "Copying tests for TOML v$TOML_VER..."
while read t; do
    echo "$t"
    mkdir -p tests/"$(dirname "$t")"
    cp -r "toml-test/tests/$t" tests/"$t"
done < "toml-test/tests/files-toml-$TOML_VER"
rm -rf toml-test
