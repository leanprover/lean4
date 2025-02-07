# Releasing a stable version

This checklist walks you through releasing a stable version.
See below for the checklist for release candidates.

We'll use `v4.6.0` as the intended release version as a running example.

- Run `scripts/release_checklist.py v4.6.0` to check the status of the release.
  This script is purely informational, idempotent, and safe to run at any stage of the release process.
- `git checkout releases/v4.6.0`
  (This branch should already exist, from the release candidates.)
- `git pull`
- In `src/CMakeLists.txt`, verify you see
  - `set(LEAN_VERSION_MINOR 6)` (for whichever `6` is appropriate)
  - `set(LEAN_VERSION_IS_RELEASE 1)`
  - (both of these should already be in place from the release candidates)
- `git tag v4.6.0`
- `git push $REMOTE v4.6.0`, where `$REMOTE` is the upstream Lean repository (e.g., `origin`, `upstream`)
- Now wait, while CI runs.
  - You can monitor this at `https://github.com/leanprover/lean4/actions/workflows/ci.yml`,
    looking for the `v4.6.0` tag.
  - This step can take up to an hour.
  - If you are intending to cut the next release candidate on the same day,
    you may want to start on the release candidate checklist now.
- Next we need to prepare the release notes.
  - If the stable release is identical to the last release candidate (this should usually be the case),
    you can reuse the release notes from `RELEASES.md`.
  - If you want to regenerate the release notes,
    use `script/release_notes.py --since v4.5.0`, run on the `releases/v4.6.0` branch,
    and see the section "Writing the release notes" below for more information.
  - Release notes should go in `RELEASES.md` on the `releases/v4.6.0` branch,
    and should also be PR'd to `master` (suggested title: "chore: update release notes for v4.6.0").
- Go to https://github.com/leanprover/lean4/releases and verify that the `v4.6.0` release appears.
  - Verify on Github that "Set as the latest release" is checked.
  - Copy the generated release note into the text box, adding the header
    ```
    v4.6.0
    ----------
    ```
- Next, we will move a curated list of downstream repos to the latest stable release.
  - In order to have the access rights to push to these repositories and merge PRs,
    you will need to be a member of the `lean-release-managers` team at both `leanprover-community` and `leanprover`.
    Contact Kim Morrison (@kim-em) to arrange access.
  - For each of the repositories listed below:
    - Make a PR to `master`/`main` changing the toolchain to `v4.6.0`
      - The usual branch name would be `bump_to_v4.6.0`.
      - Update the toolchain file
      - In the Lakefile, if there are dependencies on specific version tags of dependencies that you've already pushed as part of this process, update them to the new tag.
        If they depend on `main` or `master`, don't change this; you've just updated the dependency, so it will work and be saved in the manifest
      - Run `lake update`
      - The PR title should be "chore: bump toolchain to v4.6.0".
    - Merge the PR once CI completes.
    - Create the tag `v4.6.0` from `master`/`main` and push it.
    - Merge the tag `v4.6.0` into the `stable` branch and push it.
  - We do this for the repositories:
    - [Batteries](https://github.com/leanprover-community/batteries)
      - No dependencies
      - Toolchain bump PR
      - Create and push the tag
      - Merge the tag into `stable`
    - [lean4checker](https://github.com/leanprover/lean4checker)
      - No dependencies
      - Toolchain bump PR
      - Create and push the tag
      - Merge the tag into `stable`
    - [quote4](https://github.com/leanprover-community/quote4)
      - No dependencies
      - Toolchain bump PR
      - Create and push the tag
      - Merge the tag into `stable`
    - [doc-gen4](https://github.com/leanprover/doc-gen4)
      - Dependencies: exist, but they're not part of the release workflow
      - Toolchain bump PR including updated Lake manifest
      - Create and push the tag
      - There is no `stable` branch; skip this step
    - [Verso](https://github.com/leanprover/verso)
      - Dependencies: exist, but they're not part of the release workflow
      - The `SubVerso` dependency should be compatible with _every_ Lean release simultaneously, rather than following this workflow
      - Warnings during `lake update` and `lake build` are expected.
      - Toolchain bump PR including updated Lake manifest
      - Create and push the tag
      - There is no `stable` branch; skip this step
    - [Cli](https://github.com/leanprover/lean4-cli)
      - No dependencies
      - Toolchain bump PR
      - Create and push the tag
      - There is no `stable` branch; skip this step
    - [ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4)
      - Dependencies: `Batteries`
      - Note on versions and branches:
        - `ProofWidgets` uses a sequential version tagging scheme, e.g. `v0.0.29`,
          which does not refer to the toolchain being used.
        - Make a new release in this sequence after merging the toolchain bump PR.
        - `ProofWidgets` does not maintain a `stable` branch.
      - Toolchain bump PR
      - Create and push the tag, following the version convention of the repository
    - [Aesop](https://github.com/leanprover-community/aesop)
      - Dependencies: `Batteries`
      - Toolchain bump PR including updated Lake manifest
      - Create and push the tag
      - Merge the tag into `stable`
    - [import-graph](https://github.com/leanprover-community/import-graph)
      - Toolchain bump PR including updated Lake manifest
      - Create and push the tag
      - There is no `stable` branch; skip this step
    - [plausible](https://github.com/leanprover-community/plausible)
      - Toolchain bump PR including updated Lake manifest
      - Create and push the tag
      - There is no `stable` branch; skip this step
    - [Mathlib](https://github.com/leanprover-community/mathlib4)
      - Dependencies: `Aesop`, `ProofWidgets4`, `lean4checker`, `Batteries`, `doc-gen4`, `quote4`, `import-graph`
      - Toolchain bump PR notes:
        - Upstream dependencies should use their `main` or `master` branch, not toolchain tags.
          (Unlike for other repos.)
        - Push the PR branch to the main Mathlib repository rather than a fork, or CI may not work reliably
        - Create and push the tag
        - Create a new branch from the tag, push it, and open a pull request against `stable`.
          Coordinate with a Mathlib maintainer to get this merged.
    - [REPL](https://github.com/leanprover-community/repl)
      - Dependencies: `Mathlib` (for test code)
      - Note that there are two copies of `lean-toolchain`/`lakefile.lean`:
        in the root, and in `test/Mathlib/`. Edit both, and run `lake update` in both directories.
      - Toolchain bump PR including updated Lake manifest
      - Create and push the tag
      - Merge the tag into `stable`
- Run `script/release_checklist.py v4.6.0` again to check that everything is in order.
- Finally, make an announcement!
  This should go in https://leanprover.zulipchat.com/#narrow/stream/113486-announce, with topic `v4.6.0`.
  Please see previous announcements for suggested language.
  You will want a few bullet points for main topics from the release notes.
  If there is a blog post, link to that from the zulip announcement.
- Make sure that whoever is handling social media knows the release is out.

## Optimistic(?) time estimates:
- Initial checks and push the tag: 30 minutes.
- Waiting for the release: 60 minutes.
- Fixing release notes: 10 minutes.
- Bumping toolchains in downstream repositories, up to creating the Mathlib PR: 30 minutes.
- Waiting for Mathlib CI and bors: 120 minutes.
- Finalizing Mathlib tags and stable branch, and updating REPL: 15 minutes.
- Posting announcement and/or blog post: 20 minutes.

# Creating a release candidate.

This checklist walks you through creating the first release candidate for a version of Lean.

We'll use `v4.7.0-rc1` as the intended release version in this example.

- Decide which nightly release you want to turn into a release candidate.
  We will use `nightly-2024-02-29` in this example.
- It is essential to choose the nightly that will become the release candidate as early as possible, to avoid confusion.
- Throughout this process you can use `script/release_checklist.py v4.7.0-rc1` to track progress.
- It is essential that Batteries and Mathlib already have reviewed branches compatible with this nightly.
  - Check that both Batteries and Mathlib's `bump/v4.7.0` branch contain `nightly-2024-02-29`
    in their `lean-toolchain`.
  - The steps required to reach that state are beyond the scope of this checklist, but see below!
- Create the release branch from this nightly tag:
    ```
    git remote add nightly https://github.com/leanprover/lean4-nightly.git
    git fetch nightly tag nightly-2024-02-29
    git checkout nightly-2024-02-29
    git checkout -b releases/v4.7.0
    ```
- In `RELEASES.md` replace `Development in progress` in the `v4.7.0` section with `Release notes to be written.`
- In `src/CMakeLists.txt`,
  - verify that you see `set(LEAN_VERSION_MINOR 7)` (for whichever `7` is appropriate); this should already have been updated when the development cycle began.
  - change the `LEAN_VERSION_IS_RELEASE` line to `set(LEAN_VERSION_IS_RELEASE 1)` (this should be a change; on `master` and nightly releases it is always `0`).
  - Commit your changes to `src/CMakeLists.txt`, and push.
- `git tag v4.7.0-rc1`
- `git push origin v4.7.0-rc1`
- Now wait, while CI runs.
  - You can monitor this at `https://github.com/leanprover/lean4/actions/workflows/ci.yml`, looking for the `v4.7.0-rc1` tag.
  - This step can take up to an hour.
- (GitHub release notes) Once the release appears at https://github.com/leanprover/lean4/releases/
  - Verify that the release is marked as a prerelease (this should have been done automatically by the CI release job).
  - Generate release notes by running `script/release_notes.py --since v4.6.0` on the `releases/v4.7.0` branch.
    See the section "Writing the release notes" below for more information.
- Next, we will move a curated list of downstream repos to the release candidate.
  - This assumes that for each repository either:
    * There is already a *reviewed* branch `bump/v4.7.0` containing the required adaptations.
      The preparation of this branch is beyond the scope of this document.
    * The repository does not need any changes to move to the new version.
  - For each of the target repositories:
    - If the repository does not need any changes (i.e. `bump/v4.7.0` does not exist) then create
      a new PR updating `lean-toolchain` to `leanprover/lean4:v4.7.0-rc1` and running `lake update`.
    - Otherwise:
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
    - Once the PR has been merged, tag `master` with `v4.7.0-rc1` and push this tag.
  - We do this for the same list of repositories as for stable releases, see above.
    As above, there are dependencies between these, and so the process above is iterative.
    It greatly helps if you can merge the `bump/v4.7.0` PRs yourself!
  - It is essential for Mathlib and Batteries CI that you then create the next `bump/v4.8.0` branch
    for the next development cycle.
    Set the `lean-toolchain` file on this branch to same `nightly` you used for this release.
  - (Note: we're currently uncertain if we really want to do this step. Check with Kim Morrison if you're unsure.)
    For Batteries/Aesop/Mathlib, which maintain a `nightly-testing` branch, make sure there is a tag
    `nightly-testing-2024-02-29` with date corresponding to the nightly used for the release
    (create it if not), and then on the `nightly-testing` branch `git reset --hard master`, and force push.
- Make an announcement!
  This should go in https://leanprover.zulipchat.com/#narrow/stream/113486-announce, with topic `v4.7.0-rc1`.
  Please see previous announcements for suggested language.
  You will want a few bullet points for main topics from the release notes.
  Please also make sure that whoever is handling social media knows the release is out.
- Begin the next development cycle (i.e. for `v4.8.0`) on the Lean repository, by making a PR that:
  - Updates `src/CMakeLists.txt` to say `set(LEAN_VERSION_MINOR 8)`
  - Replaces the "release notes will be copied" text in the `v4.6.0` section of `RELEASES.md` with the
    finalized release notes from the `releases/v4.6.0` branch.
  - Replaces the "development in progress" in the `v4.7.0` section of `RELEASES.md` with
    ```
    Release candidate, release notes will be copied from the branch `releases/v4.7.0` once completed.
    ```
    and inserts the following section before that section:
    ```
    v4.8.0
    ----------
    Development in progress.
    ```
  - Removes all the entries from the `./releases_drafts/` folder.
  - Titled "chore: begin development cycle for v4.8.0"


## Time estimates:
Slightly longer than the corresponding steps for a stable release.
Similar process, but more things go wrong.
In particular, updating the downstream repositories is significantly more work
(because we need to merge existing `bump/v4.7.0` branches, not just update a toolchain).

# Preparing `bump/v4.7.0` branches

While not part of the release process per se,
this is a brief summary of the work that goes into updating Batteries/Aesop/Mathlib to new versions.

Please read https://leanprover-community.github.io/contribute/tags_and_branches.html

* Each repo has an unreviewed `nightly-testing` branch that
  receives commits automatically from `master`, and
  has its toolchain updated automatically for every nightly.
  (Note: the aesop branch is not automated, and is updated on an as needed basis.)
  As a consequence this branch is often broken.
  A bot posts in the (private!) "Mathlib reviewers" stream on Zulip about the status of these branches.
* We fix the breakages by committing directly to `nightly-testing`: there is no PR process.
  * This can either be done by the person managing this process directly,
    or by soliciting assistance from authors of files, or generally helpful people on Zulip!
* Each repo has a `bump/v4.7.0` which accumulates reviewed changes adapting to new versions.
* Once `nightly-testing` is working on a given nightly, say `nightly-2024-02-15`, we will create a PR to `bump/v4.7.0`.
* For Mathlib, there is a script in `scripts/create-adaptation-pr.sh` that automates this process.
* For Batteries and Aesop it is currently manual.
* For all of these repositories, the process is the same:
  * Make sure `bump/v4.7.0` is up to date with `master` (by merging `master`, no PR necessary)
  * Create from `bump/v4.7.0` a `bump/nightly-2024-02-15` branch.
  * In that branch, `git merge nightly-testing` to bring across changes from `nightly-testing`.
  * Sanity check changes, commit, and make a PR to `bump/v4.7.0` from the `bump/nightly-2024-02-15` branch.
  * Solicit review, merge the PR into `bump/v4.7.0`.
* It is always okay to merge in the following directions:
  `master` -> `bump/v4.7.0` -> `bump/nightly-2024-02-15` -> `nightly-testing`.
  Please remember to push any merges you make to intermediate steps!

# Writing the release notes

Release notes are automatically generated from the commit history, using `script/release_notes.py`.

Run this as `script/release_notes.py --since v4.6.0`, where `v4.6.0` is the *previous* release version.
This script should be run on the `releases/v4.7.0` branch.
This will generate output for all commits since that tag.
Note that there is output on both stderr, which should be manually reviewed,
and on stdout, which should be manually copied to `RELEASES.md`.

The output on stderr should mostly be about commits for which the script could not find an associated PR,
usually because a PR was rebase-merged because it contained an update to stage0.
Some judgement is required here: ignore commits which look minor,
but manually add items to the release notes for significant PRs that were rebase-merged.

There can also be pre-written entries in `./releases_drafts`, which should be all incorporated in the release notes and then deleted from the branch.
  See `./releases_drafts/README.md` for more information.

# `release_checklist.py`

The script `script/release_checklist.py` attempts to automate checking the status of the release.

Future improvements:
* We check the release notes have been posted on Github,
  but do not check that they are present in `RELEASES.md` on the release branch or on `master`.
