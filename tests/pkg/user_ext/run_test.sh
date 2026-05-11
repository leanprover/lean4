rm -rf .lake

capture lake build -v
check_out_contains 'hello, test, world'
