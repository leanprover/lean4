rm -rf .lake

run lake exe release
run_fail lake exe debug
