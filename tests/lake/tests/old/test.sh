#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test the `--old` option for using outdate oleans
# https://github.com/leanprover/lake/issues/44
# https://github.com/leanprover/lean4/issues/2822

diff_out() {
  grep 'Built' || true |
  sed 's/^.*\[.*\] //' |
  sed 's/\s*(.*)$//' |
  LANG=POSIX sort |
  diff -u --strip-trailing-cr "$1" -
}

$LAKE new hello
$LAKE -d hello build
sleep 1 # sleep needed to guarantee modification time difference

# Test basic `--old`
echo 'def hello := "old"' > hello/Hello/Basic.lean
$LAKE -d hello build --old | diff_out <(cat << 'EOF'
Built Hello.Basic
Built Hello.Basic:c
Built hello
EOF
)

# Test a normal build works after an `--old` build
echo 'def hello := "normal"' > hello/Hello/Basic.lean
$LAKE -d hello build | diff_out <(cat << 'EOF'
Built Hello
Built Hello.Basic
Built Hello.Basic:c
Built Main
Built hello
EOF
)

# Test that `--old` does not rebuild touched but unchanged files (lean4#2822)
touch hello/Hello/Basic.lean
$LAKE -d hello build --old | diff_out /dev/null
