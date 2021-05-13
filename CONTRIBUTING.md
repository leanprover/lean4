# Contribution Guidelines

Thank you for your interest in contributing to Lean! There are many ways to contribute and we appreciate all of them.

## Bug reports

Bug reports as new issues are always welcome. Please check the existing [issues](https://github.com/leanprover/lean4/issues) first.
Reduce the issue to a self-contained, reproducible test case.
If you have the chance, before reporting a bug, please search existing issues, as it's possible that
someone else has already reported your error.
If you're not sure if something is a bug or not, feel free to file a bug anyway. You may also want to discuss it with the Lean
community using the [lean4 Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4).

## Simple fixes

Simple fixes for **typos and clear bugs** are welcome.

## Documentation

Tutorial-like examples are very welcome.
They are useful for finding rough edges and bugs in Lean 4, for highlighting new features, and for showing how to use Lean.
If you want to store your tutorial in the Lean 4 repository to make sure future changes will not break it, we suggest the following workflow:
* Contact one of the Lean developers on Zulip, and check whether your tutorial is a good match for the Lean 4 repository.
* Send bug reports and report rough edges. We will work with you until the tutorial looks great.
* Add plenty of comments and make sure others will be able to follow it.
* Create a pull request in the Lean 4 repository. After merging, we will link it to the official documentation and make sure it becomes part of our test suite.

You can use `.lean` or `.md` files to create your tutorial. The `.md` files are ideal when you want to format your prose using markdown. For an example, see [this `.md` file](https://github.com/leanprover/lean4/blob/master/doc/lean3changes.md).

Contributions to the reference manual are also welcome, but since Lean 4 is changing rapidly, please contact us first using Zulip
to find out which parts are stable enough to document. We will work with you to get this kind of
pull request merged. We are also happy to meet using Zoom, Skype or Google hangout to coordinate this kind of effort.

As Lean 4 matures, other forms of documentation (e.g., doc-strings) will be welcome too.

## "Help wanted"

For issues marked as [`help wanted`](https://github.com/leanprover/lean4/issues?q=is%3Aissue+is%3Aopen+label%3A%22help+wanted%22), pull requests (PR) are welcome and we will work with you to get a PR merged. Some of these issues are nontrivial. If you are interested, please consider adding comments to the issue and/or messaging the Lean developers in [Zulip](https://leanprover.zulipchat.com/#).

## Unexpected Pull Requests

We have very few core developers, and we cannot review arbitrary pull requests (PRs). Moreover, many features involve subtle tradeoffs, and it may require significant time and energy to even assess a proposed design. We suggest the following workflow:

* First, discuss your idea with the Lean community on Zulip. Ask the community to help collect examples, document the requirements, and detect complications.
* If there is broad support, create a detailed issue for it on the Lean 4 repository at GitHub, and tag the issue with `RFC`.
* Ask the community for help documenting the requirements, and for collecting examples and concerns.
* Wait for one of the core developers to give you a "go ahead". At this point, the core developers will work with you to make sure your PR gets merged.

We don't want to waste your time by you implementing a feature and then us not being able to merge it.

## How to Contribute

* Always follow the [commit convention](https://leanprover.github.io/lean4/doc/commit_convention.html).
* Follow the style of the surrounding code. When in doubt, look at other files using the particular syntax as well.
* Make sure your code is documented.
* New features or bug fixes should come with appropriate tests.
* Ensure all tests work before submitting a PR; see [Development Setup](https://leanprover.github.io/lean4/doc/make/index.html#development-setup) and [Fixing Tests](https://leanprover.github.io/lean4/doc/fixing_tests.html).
