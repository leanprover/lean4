rm -rf .lake/build

capture lake build -v
check_out_contains 'hello, test, world'
