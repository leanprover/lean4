To upgrade Lean's LLVM version we currently perform the following steps:
1. Make PR to leanprover/lean-llvm that upgrades the LLVM version, example: https://github.com/leanprover/lean-llvm/pull/15
2. Merge PR to master, create a tag with the LLVM version name and wait for CI to create the release on that tag, example: https://github.com/leanprover/lean-llvm/releases/tag/22.1.4
3. Got to leanprover/lean4 and update all necessary LLVM things there, this is currently:
  - bumping the llvm-urls in `.github/workflows/ci.yml`
  - bumping `LLVM_RELEASE` in `tests/bench_build.sh` and `tests/bench_other.sh`
  - fixing potential build failures
4. Create a PR and run `!bench` to see performance impact, example: https://github.com/leanprover/lean4/pull/13545
5. Run `release-ci` on the PR to ensure everything still works on all platforms
6. Profit!

Note: you might want to create a prerelease tag on lean-llvm and work with that until you are sure
the bump is actually going to work.

