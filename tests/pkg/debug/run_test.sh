rm -rf .lake

run_fail lake env lean invalid.lean
run lake exe release
run_fail lake exe debug
