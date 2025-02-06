# Read this section before submitting

* Ensure your PR follows the [External Contribution Guidelines](https://github.com/leanprover/lean4/blob/master/CONTRIBUTING.md).
* Please make sure the PR has excellent documentation and tests. If we label it `missing documentation` or `missing tests` then it needs fixing!
* Include the link to your `RFC` or `bug` issue in the description.
* If the issue does not already have approval from a developer, submit the PR as draft.
* The PR title/description will become the commit message. Keep it up-to-date as the PR evolves.
* For `feat/fix` PRs, the first paragraph starting with "This PR" must be present and will become a
  changelog entry unless the PR is labeled with `no-changelog`. If the PR does not have this label,
  it must instead be categorized with one of the `changelog-*` labels (which will be done by a
  reviewer for external PRs).
* A toolchain of the form `leanprover/lean4-pr-releases:pr-release-NNNN` for Linux and M-series Macs will be generated upon build. To generate binaries for Windows and Intel-based Macs as well, write a comment containing `release-ci` on its own line.
* If you rebase your PR onto `nightly-with-mathlib` then CI will test Mathlib against your PR.
* You can manage the `awaiting-review`, `awaiting-author`, and `WIP` labels yourself, by writing a comment containing one of these labels on its own line.
* Remove this section, up to and including the `---` before submitting.

---

This PR <short changelog summary for feat/fix, see above>.

Closes <`RFC` or `bug` issue number fixed by this PR, if any>
