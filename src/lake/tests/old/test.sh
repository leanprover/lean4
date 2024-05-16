#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

diff_out() {
  sed 's/^.*\[.*\] //' |
  sed 's/\s*(.*)$//' |
  diff -u --strip-trailing-cr "$1" -
}

# Test the `--old` option for using outdate oleans
# https://github.com/leanprover/lake/issues/44
# https://github.com/leanprover/lean4/issues/2822

$LAKE new hello
$LAKE -d hello build
sleep 1 # sleep needed to guarantee modification time difference

# Test basic `--old`
echo 'def hello := "old"' > hello/Hello/Basic.lean
$LAKE -d hello build --old | diff_out <(cat << 'EOF'
Built Hello.Basic
Built Hello.Basic:c
Built hello
Build completed successfully.
EOF
)

# Test a normal build works after an `--old` build
echo 'def hello := "normal"' > hello/Hello/Basic.lean
$LAKE -d hello build | diff_out <(cat << 'EOF'
Built Hello.Basic
Built Hello
Built Hello.Basic:c
Built Main
Built hello
Build completed successfully.
EOF
)

# Test that `--old` does not rebuild touched but unchanged files (lean4#2822)
touch hello/Hello/Basic.lean
$LAKE -d hello build --old | diff_out <(cat << 'EOF'
Build completed successfully.
EOF
)
