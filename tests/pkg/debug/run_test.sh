rm -rf .lake/build

run lake exe release
run_fail lake exe debug
