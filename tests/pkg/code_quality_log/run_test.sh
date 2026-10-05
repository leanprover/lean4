rm -rf .lake

# Builds both libraries; the `#guard_msgs` checks in the test modules run as part of the build.
lake build

# The entries captured per command are merged into each module's final environment by
# `runFrontend`; check what was persisted into the `.olean`s, in command order. (The two test
# modules declare the same names, so they are inspected separately.)
capture lake env lean --run PrintEntries.lean CQTest.TestAsync
check_out_contains "CQTest.TestAsync: [linter.cqTest/a1, _/raw:a1, linter.cqTest/stateful:a1:1, linter.cqTest/a2, _/raw:a2, linter.cqTest/stateful:a2:2, _/raw:hidden]"
capture lake env lean --run PrintEntries.lean CQTestSync.TestSync
check_out_contains "CQTestSync.TestSync: [linter.cqTest/s1, _/raw:s1, linter.cqTest/stateful:s1:1, linter.cqTest/s2, _/raw:s2, linter.cqTest/stateful:s2:2, _/raw:hidden]"
