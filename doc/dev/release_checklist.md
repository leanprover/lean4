# Releasing a stable version

This checklist walks you through releasing a stable version.
See below for the checklist for release candidates.

We'll use `v4.6.0` as the intended release version as a running example.

- `git checkout releases/v4.6.0`
  (This branch should already exist, from the release candidates.)
- `git pull`
- In `src/CMakeLists.txt`, verify you see
  - `set(LEAN_VERSION_MINOR 6)` (for whichever `6` is appropriate)
  - `set(LEAN_VERSION_IS_RELEASE 1)`
  - (both of these should already be in place from the release candidates)
- Run `git diff master RELEASES.md`.
  - You should expect to see changes in the `v4.7.0-rc1` section, which you may ignore.
    (i.e. the new release notes for the upcoming release candidate).
  - But if there are discrepancies in the `v4.6.0` section, you should reconcile these, either by:
    - Using `git cherry-pick` to pull the commits that modified the release notes on `master`
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
- Finally, make an announcement!
  This should go in https://leanprover.zulipchat.com/#narrow/stream/113486-announce, with topic `v4.6.0`.
  Please see previous announcements for suggested language.
  You will want a few bullet points for main topics from the release notes.
  If you are making a blog post, that should be coordinated with the announcement on Zulip and linked from there.
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

TODO:
* Downstream repositories: merging `bump/v4.7.0` branches to `master`/`main`
* Announcements
* Begin development cycle for next version

TODO:
* More documentation on ensuring the `bump/v4.7.0` branches are ready in time for the release candidate.

TODO:
* Time estimates


