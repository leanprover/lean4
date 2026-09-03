rm -rf .lake

# Build the library; the linter registered in `FindMatchingDecl.Linter` runs on each
# command of `FindMatchingDecl` and reports the declaration `findMatchingDecl?` picks.
capture lake build

check_out_contains "FindMatchingDecl.lean:7:0: best match is: a"
check_out_contains "FindMatchingDecl.lean:8:0: best match is: b"
check_out_contains "FindMatchingDecl.lean:9:0: best match is: c"
check_out_contains "FindMatchingDecl.lean:11:0: best match is: Foo"
# The whole `mutual` command resolves to the earliest declaration in the block.
check_out_contains "FindMatchingDecl.lean:14:0: best match is: hello2"
check_out_contains "FindMatchingDecl.lean:22:0: best match is: Magma"
# An anonymous instance resolves to its generated name.
check_out_contains "FindMatchingDecl.lean:25:0: best match is: instMagmaNat"
