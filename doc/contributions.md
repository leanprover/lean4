# Contribution Guidelines

Thank you for your interest in contributing to Lean! There are many ways to contribute and we appreciate all of them.

* [Asking questions](#asking-questions)
* [Cloning and building](#cloning-and-building)
* [Contributing](#contributing)
  * [Bug reports](#bug-reports)
  * [Bug fixes](#bug-fixes)
  * [Feature requests](#feature-requests)
  * [Feature implementations](#feature-implementations)
  * [Documentation updates](#documentation-updates)
* [Workflows](#workflows)
  * [Making commits](#making-commits)
  * [Submitting pull requests](#submitting-pull-requests)

## Asking questions

If you have questions, please make a post on the [Lean Zulip server](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4).

**Please ask questions!** A lot of people report feeling that they are "wasting expert time", but nobody on the team feels this way. Contributors are important to us.

Also, your questions will help other people, since they will be able to find the answers quickly.

We do ask that you be mindful to include as much useful information as you can in your question, but we recognize this can be hard if you are unfamiliar with contributing to Lean.

## Cloning and building

Please refer to "[Development workflow](./dev/index.md)".

## Contributing

### Bug reports

Bug reports as new issues are always welcome.

* Please check [the existing issues](https://github.com/leanprover/lean4/issues) first.
* Reduce the issue to a self-contained, reproducible test case.

If you're not sure if something is a bug or not, feel free to file a bug anyway. You may also want to discuss it with the Lean community [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4).

### Bug fixes

* Follow "[Submitting pull requests](#submitting-pull-requests)".

### Feature requests

If you're willing to implement the feature, please refer to [Feature implementations](#feature-implementations). Otherwise, we kindly ask you not to submit a feature request, since we're prioritizing active PRs with code.

### Feature implementations

* [Create a new topic on Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4) to discuss your idea with the Lean community.
  * Prefix your topic name with "RFC: ".
* If there is broad support, [create an issue on GitHub](https://github.com/leanprover/lean4/issues/new/choose).
  * Prefix the issue name with "RFC: "
  * Tag the issue with `RFC`.
* Wait for one of the core developers to give you a "go ahead".
* Follow "[Submitting pull requests](#submitting-pull-requests)".

After this, the core developers will work with you to make sure your PR gets merged.

When creating a RFC, consider the following questions:

* **User Experience**: How does this feature improve the user experience?
* **Beneficiaries**: Which Lean users and projects do benefit most from this feature?
* **Community Feedback**: What do other Lean users think about this feature?
* **Maintainability**: Are the benefits higher than costs for this feature?

### Documentation updates

Documentation is very important - it's the first thing the person reads when starting out with Lean. Therefore, we highly welcome improvements & expansions of the existing docs. Please follow the guidelines for specific documentation types:

* [Docstrings](#docstrings)
* [Tutorials](#tutorials)
* [References](#references)

#### Docstrings

Docstrings are special comments that may appear above definitions in the Lean code. They are helpful for getting in-context help during development, as they are displayed in the inline popups. Currently we don't have any specific requirements for docstrings; feel free to use them to explain the definitions in your own words (including using non-technical language).

#### Tutorials

Tutorial-like examples are very welcome. They are useful for finding rough edges and bugs in Lean 4, for highlighting new features, and for showing how to use Lean.

If you want to store your tutorial in the Lean 4 repository to make sure future changes will not break it, we suggest the following workflow:

* Contact one of the Lean developers [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4), and check whether your tutorial is a good match for the Lean 4 repository.
* Send bug reports and report rough edges. We will work with you until the tutorial looks great.
* Add plenty of comments and make sure others will be able to follow it.
* Create a pull request in the Lean 4 repository. After merging, we will link it to the official documentation and make sure it becomes a part of our test suite.

You can use `.lean` or `.md` files to create your tutorial. The `.md` files are ideal when you want to format your prose using markdown. For an example, see [this `.md` file](https://github.com/leanprover/lean4/blob/master/doc/lean3changes.md).

#### References

Contributions to the reference manual are also welcome, but since Lean 4 is changing rapidly, please [contact us first](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4) to find out which parts are stable enough to document. We will work with you to get this kind of pull request merged. We are also happy to meet using Zoom, Skype or Google hangout to coordinate this kind of effort.

## Workflows

### Making commits

* Follow the [commit convention](./dev/commit_convention.md).
* Follow the style of the surrounding code. When in doubt, look at other files using the particular syntax as well.
* Try reusing existing definitions from [the Lean compiler](https://github.com/leanprover/lean4), [Std](https://github.com/leanprover/std4), [Mathlib](https://github.com/leanprover-community/mathlib4).
* Check that your changes do not introduce performance regressions.
* Add docstrings to non-trivial definitions.
* Add tests for non-trivial cases (see "[Testing](./dev/testing.md)").

### Submitting pull requests

See also: [Making commits](#making-commits)

* Sync your fork with the main repository.
* Check that all tests pass (see "[Fixing tests](./dev/testing.md#fixing-tests)").
* Check that the pull request contains a single, clearly-defined issue or feature.
* Provide a descriptive title & summary. If the proposed change has already been discussed on Zulip, please summarize the discussion (don't just drop a link).
* Reference any issues that your PR addresses to provide context.
* After submitting, ensure that all CI checks pass on your PR.

Once the PR is submitted, please stay responsive to feedback and be prepared to make necessary revisions. We will close any PR that has been inactive (no response or updates from the submitter) for more than a month.

What to expect:

* Feedback: we may ask you to improve the PR to match the code quality standards.
* Time: we try to respond to every PR, but we can't promise a specific timeframe.
* Merge: we try to merge most PRs, but we can't promise to merge every single PR. To improve the chances of your PR getting merged, please ensure your changes align with the project's goals and quality standards.

**Thank you for contributing!**
