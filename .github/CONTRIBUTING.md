# Contributing to Lean

Thank you for choosing to contribute to Lean. This document is intended as a brief guide
for new contributors to help streamline the process and make it as easy as possible
for you (the contributors) and us (the maintainers).

### Writing Code

- [Coding Style](../doc/coding_style.md)
- [Library Style Conventions](../doc/lean/library_style.org)
- [Git Commit Conventions](../doc/commit_convention.md)
- [Automatic Builds](../doc/make/travis.md)

# Opening Issues

-  Checked that your issue isn't [already filed](https://github.com/leanprover/lean/issues).
- Specifically look over:
  * the [wishlist](https://github.com/leanprover/lean/issues?q=is%3Aissue+is%3Aopen+label%3AI-wishlist),
  * open [RFCs](https://github.com/leanprover/lean/issues?q=is%3Aissue+is%3Aopen+label%3ARFC),
  * open [feature requests](https://github.com/leanprover/lean/issues?q=is%3Aissue+is%3Aopen+label%3AFeature).
- Reduce the issue to a self-contained, reproducible test case.

# Opening Pull Requests

The core developers have to maintain Lean. Thus, they need to read all PRs, and make sure they can maintain them.
So, here are some guidelines for submitting PRs:
- Small bug fixes are always welcome.
- Before implementing a major feature or refactoring the code, please ask whether the change is welcome or not.
  The worst kind of PR is the "unwanted one". That is, we don’t want it, but we have to explain why we will not merge it.
- Ensure all tests work before submitting a PR. You can run the test suite (after building Lean and the Lean library) by calling `ctest` in your build directory.
- Ensure your Pull Request meets the coding and commit conventions documented above.
- Ensure your Pull Request contains tests for the behavior, for both features or
  bug fixes.
- If you are not proficient in C++, do not submit PRs with C++ code.
