# Releasing a stable version

This checklist walks you through releasing a stable version.
See below for the checklist for release candidates.

We'll use `v4.6.0` as the intended release version as a running example.

- One week before the planned release, ensure that someone has written the first draft of the release blog post
- `git checkout releases/v4.6.0`
  (This branch should already exist, from the release candidates.)
- `git pull`
- In `src/CMakeLists.txt`, verify you see
  - `set(LEAN_VERSION_MINOR 6)` (for whichever `6` is appropriate)
  - `set(LEAN_VERSION_IS_RELEASE 1)`
  - (both of these should already be in place from the release candidates)
- It is possible that the `v4.6.0` section of `RELEASES.md` is out of sync between
  `releases/v4.6.0` and `master`. This should be reconciled:
  - Run `git diff master RELEASES.md`.
  - You should expect to see changes in the `v4.7.0-rc1` section
    (i.e. the new release notes for the upcoming release candidate).
  - Reconcile discrepancies in the `v4.6.0` section, either by:
    - Using `git cherry-pick` to pull the commits that modified the release notes on `master`.
    - Simply pushing a new commit to `releases/v4.6.0`.
- `git tag v4.6.0`
- `git push origin v4.6.0`
- Now wait, while CI runs.
  - You can monitor this at `https://github.com/leanprover/lean4/actions/workflows/ci.yml`,
    looking for the `v4.6.0` tag.
  - This step can take up to an hour.
  - If you are intending to cut the next release candidate on the same day,
    you may want to start on the release candidate checklist now.
- Go to https://github.com/leanprover/lean4/releases and verify that the `v4.6.0` release appears.
  - The automatically generated release notes there will not be useful!
  - Copy and paste the `v4.6.0` section from `RELEASES.md` into the GitHub release notes.
  - Use the title "Changes since v4.5.0 (from RELEASES.md)"
- Next, we will move a curated list of downstream repos to the latest stable release.
  - For each of the repositories listed below:
    - Make a PR to `master`/`main` changing the toolchain to `v4.6.0`.
      The PR title should be "chore: bump toolchain to v4.6.0".
      Since the `v4.6.0` release should be functionally identical to the last release candidate,
      which the repository should already be on, this PR is a no-op besides changing the toolchain.
    - Once this is merged, create the tag `v4.6.0` from `master`/`main` and push it.
    - Merge the tag `v4.6.0` into the stable branch.
  - We do this for the repositories:
    - [lean4checker](https://github.com/leanprover/lean4checker)
      - `lean4checker` uses a different version tagging scheme: use `toolchain/v4.6.0` rather than `v4.6.0`.
    - [Std](https://github.com/leanprover-community/repl)
    - [ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4)
      - `ProofWidgets` uses a sequential version tagging scheme, e.g. `v0.0.29`,
        which does not refer to the toolchain being used.
      - Make a new release in this sequence after merging the toolchain bump PR.
      - `ProofWidgets` does not maintain a `stable` branch.
    - [Aesop](https://github.com/leanprover-community/aesop)
    - [Mathlib](https://github.com/leanprover-community/mathlib4)
      - In addition to updating the `lean-toolchain` and `lakefile.lean`,
        in `.github/workflows/build.yml.in` in the `lean4checker` section update the line
        `git checkout toolchain/v4.6.0` to the appropriate tag,
        and then run `.github/workflows/mk_build_yml.sh`.
    - [REPL](https://github.com/leanprover-community/repl)
      - Note that there are two copies of `lean-toolchain`/`lakefile.lean`:
        in the root, and in `test/Mathlib/`.
  - Note that there are dependencies between these packages:
    you should update the lakefile so that you are using the `v4.6.0` tag of upstream repositories
    (or the sequential tag for `ProofWidgets4`), and run `lake update` before committing.
  - This means that this process is sequential; each repository must have its bump PR merged,
    and the new tag pushed, before you can make the PR for the downstream repositories.
    - `lean4checker` has no dependencies
    - `Std` has no dependencies
    - `Aesop` depends on `Std`
    - `ProofWidgets4` depends on `Std`
    - `Mathlib` depends on `Aesop`, `ProofWidgets4`, and `lean4checker` (and transitively on `Std`)
    - `REPL` depends on `Mathlib` (this dependency is only for testing).
- Merge the release announcement PR for the Lean website - it will be deployed automatically
- Finally, make an announcement!
  This should go in https://leanprover.zulipchat.com/#narrow/stream/113486-announce, with topic `v4.6.0`.
  Please see previous announcements for suggested language.
  You will want a few bullet points for main topics from the release notes.
  Link to the blog post from the Zulip announcement.
  Please also make sure that whoever is handling social media knows the release is out.

## Optimistic time estimates:
- Initial checks and push the tag: 30 minutes.
- Note that if `RELEASES.md` has discrepancies this could take longer!
- Waiting for the release: 60 minutes.
- Fixing release notes: 15 minutes.
- Bumping toolchains in downstream repositories, up to creating the Mathlib PR: 30 minutes.
- Waiting for Mathlib CI and bors: 120 minutes.
- Finalizing Mathlib tags and stable branch, and updating REPL: 15 minutes.
- Posting announcement and/or blog post: 20 minutes.

# Creating a release candidate.

This checklist walks you through creating the first release candidate for a version of Lean.

We'll use `v4.7.0-rc1` as the intended release version in this example.

- Decide which nightly release you want to turn into a release candidate.
  We will use `nightly-2024-02-29` in this example.
- It is essential that Std and Mathlib already have reviewed branches compatible with this nightly.
  - Check that both Std and Mathlib's `bump/v4.7.0` branch contain `nightly-2024-02-29`
    in their `lean-toolchain`.
  - The steps required to reach that state are beyond the scope of this checklist!
- Create the release branch from this nightly tag:
    ```
    git remote add nightly https://github.com/leanprover/lean4-nightly.git
    git fetch nightly tag nightly-2024-02-29
    git checkout nightly-2024-02-29
    git checkout -b releases/v4.7.0
    ```
- In `RELEASES.md` remove `(development in progress)` from the `v4.7.0` section header.
- Unfortunately, we are not yet consistent about updating `RELEASES.md` as part of each feature PR, so there may be manual work at this stage updating it.
  - Do not wait on `RELEASES.md` being perfect before creating the `release/v4.7.0` branch. It is essential to choose the nightly which will become the release candidate as early as possible, to avoid confusion.
  - You may like to solicit updates to `RELEASES.md` from other developers. Ideally these will land on `master` before the nightly.
  - I will usually go through the list of all PRs merged since the previous release branch `releases/v4.6.0`.
  Many PRs do not warrant mention in `RELEASES.md`. For many medium scale PRs, it suffices to just copy and paste the title, along with a link. (See existing format in `RELEASES.md`.) If you find something major that has not been mentioned, it may require correspondence with the author of that PR to prepare a good paragraph.
  - Commit your changes to `RELEASES.md`, and push.
  - Remember that changes to `RELEASES.md` after you have branched `releases/v4.7.0` should also be cherry-picked back to `master`.
- In `src/CMakeLists.txt`,
  - verify that you see `set(LEAN_VERSION_MINOR 7)` (for whichever `7` is appropriate); this should already have been updated when the development cycle began.
  - `set(LEAN_VERSION_IS_RELEASE 1)` (this should be a change; on `master` and nightly releases it is always `0`).
  - Commit your changes to `src/CMakeLists.txt`, and push.
- `git tag v4.7.0-rc1`
- `git push origin v4.7.0-rc1`
- Now wait, while CI runs.
  - You can monitor this at `https://github.com/leanprover/lean4/actions/workflows/ci.yml`, looking for the `v4.7.0-rc1` tag.
  - This step can take up to an hour.
- Once the release appears at https://github.com/leanprover/lean4/releases/
  - Edit the release notes on Github to select the "Set as a pre-release box".
  - Copy the section of `RELEASES.md` for this version into the Github release notes.
- Next, we will move a curated list of downstream repos to the release candidate.
  - This assumes that there is already a *reviewed* branch `bump/v4.7.0` on each repository
    containing the required adaptations (or no adaptations are required).
    The preparation of this branch is beyond the scope of this document.
  - For each of the target repositories:
    - Checkout the `bump/v4.7.0` branch.
    - Verify that the `lean-toolchain` is set to the nightly from which the release candidate was created.
    - `git merge origin/master`
    - Change the `lean-toolchain` to `leanprover/lean4:v4.7.0-rc1`
    - In `lakefile.lean`, change any dependencies which were using `nightly-testing` or `bump/v4.7.0` branches
      back to `master` or `main`, and run `lake update` for those dependencies.
    - Run `lake build` to ensure that dependencies are found (but it's okay to stop it after a moment).
    - `git commit`
    - `git push`
    - Open a PR from `bump/v4.7.0` to `master`, and either merge it yourself after CI, if appropriate,
      or notify the maintainers that it is ready to go.
    - Once this PR has been merged, tag `master` with `v4.7.0-rc1` and push this tag.
  - We do this for the same list of repositories as for stable releases, see above.
    As above, there are dependencies between these, and so the process above is iterative.
    It greatly helps if you can merge the `bump/v4.7.0` PRs yourself!
  - For Std/Aesop/Mathlib, which maintain a `nightly-testing` branch, make sure there is a tag
    `nightly-testing-2024-02-29` with date corresponding to the nightly used for the release
    (create it if not), and then on the `nightly-testing` branch `git reset --hard master`, and force push.
- Make an announcement!
  This should go in https://leanprover.zulipchat.com/#narrow/stream/113486-announce, with topic `v4.7.0-rc1`.
  Please see previous announcements for suggested language.
  You will want a few bullet points for main topics from the release notes.
  Please also make sure that whoever is handling social media knows the release is out.
- Begin the next development cycle (i.e. for `v4.8.0`) on the Lean repository, by making a PR that:
  - Updates `src/CMakeLists.txt` to say `set(LEAN_VERSION_MINOR 8)`
  - Removes `(in development)` from the section heading in `RELEASES.md` for `v4.7.0`,
    and creates a new `v4.8.0 (in development)` section heading.

TODO:
* More documentation on ensuring the `bump/v4.7.0` branches are ready in time for the release candidate.

TODO:
* Time estimates


