rm -rf .lake
lake build

# Without full initialization of the Lean package (which is linked into the executable even though
# it is not visibly imported into the root module), running the executable crashes.
capture ./.lake/build/bin/main
check_out_contains "empty env has no Nat: true"
