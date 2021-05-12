# Contribution Guidelines

## What to Contribute

* **Bug reports** as new issues are always welcome, but nitpicking issues are not (e.g., the error message is confusing). Please check the existing issues first. Reduce the issue to a self-contained, reproducible test case.
* Simple fixes for **typos and clear bugs** are welcome if they don't increase maintenance.
* Extensions to **docs & docstrings** are welcome if you are relatively sure about their correctness; if you need to guess, it can often take longer to correct the content than for us to write it ourselves.
* For issues marked as `help wanted`, PRs are welcome and we will work with you to get a PR merged.
* Other PRs regarding **non-trivial features** are **not welcome** without prior communication. We don't want to waste your time by you implementing a feature and then us not being able to merge it because of the reasons mentioned in [Should I use Lean?](https://leanprover.github.io/lean4/doc/faq.html). If you have an idea for a feature that is clearly in line with Lean's direction and want to implement it, please open an issue for it first. If you are not sure about compatibility with our plans, the `#lean4` channel on Zulip is a good way to gauge initial interest & feasibility. In either case, be prepared for us not to respond or to reject the proposal with only a brief comment.

## How to Contribute

* Always follow the [commit convention](https://leanprover.github.io/lean4/doc/commit_convention.html).
* Follow the style of the surrounding code. When in doubt, look at other files using the particular syntax as well.
* New features or bug fixes should come with appropriate tests.
* Ensure all tests work before submitting a PR; see [Development Setup](https://leanprover.github.io/lean4/doc/make/index.html#development-setup) and [Fixing Tests](https://leanprover.github.io/lean4/doc/fixing_tests.html).
