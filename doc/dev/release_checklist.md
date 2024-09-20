# Releasing a stable version

This checklist walks you through releasing a stable version.
See below for the checklist for release candidates.

We'll use `v4.6.0` as the intended release version as a running example.

- One week before the planned release, ensure that
  (1) someone has written the release notes and
  (2) someone has written the first draft of the release blog post.
  If there is any material in `./releases_drafts/` on the `releases/v4.6.0` branch, then the release notes are not done.
  (See the section "Writing the release notes".)
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
- Go to https://github.com/leanprover/lean4/releases and verify that the `v4.6.0` release appears.
  - Edit the release notes on Github to select the "Set as the latest release".
  - Follow the instructions in creating a release candidate for the "GitHub release notes" step,
    now that we have a written `RELEASES.md` section.
    Do a quick sanity check.
- Next, we will move a curated list of downstream repos to the latest stable release.
  - For each of the repositories listed below:
    - Make a PR to `master`/`main` changing the toolchain to `v4.6.0`
      - Update the toolchain file
      - In the Lakefile, if there are dependencies on specific version tags of dependencies that you've already pushed as part of this process, update them to the new tag.
        If they depend on `main` or `master`, don't change this; you've just updated the dependency, so it will work and be saved in the manifest
      - Run `lake update`
      - The PR title should be "chore: bump toolchain to v4.6.0".
    - Merge the PR once CI completes.
    - Create the tag `v4.6.0` from `master`/`main` and push it.
    - Merge the tag `v4.6.0` into the `stable` branch and push it.
  - We do this for the repositories:
    - [lean4checker](https://github.com/leanprover/lean4checker)
      - No dependencies
      - Toolchain bump PR
      - Create and push the tag
      - Merge the tag into `stable`
    - [Batteries](https://github.com/leanprover-community/batteries)
      - No dependencies
      - Toolchain bump PR
      - Create and push the tag
      - Merge the tag into `stable`
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
    - [doc-gen4](https://github.com/leanprover/doc-gen4)
      - Dependencies: exist, but they're not part of the release workflow
      - Toolchain bump PR including updated Lake manifest
      - Create and push the tag
      - There is no `stable` branch; skip this step
    - [Verso](https://github.com/leanprover/verso)
      - Dependencies: exist, but they're not part of the release workflow
      - The `SubVerso` dependency should be compatible with _every_ Lean release simultaneously, rather than following this workflow
      - Toolchain bump PR including updated Lake manifest
      - Create and push the tag
      - There is no `stable` branch; skip this step
    - [import-graph](https://github.com/leanprover-community/import-graph)
      - Toolchain bump PR including updated Lake manifest
      - Create and push the tag
      - There is no `stable` branch; skip this step
    - [Mathlib](https://github.com/leanprover-community/mathlib4)
      - Dependencies: `Aesop`, `ProofWidgets4`, `lean4checker`, `Batteries`, `doc-gen4`, `import-graph`
      - Toolchain bump PR notes:
        - In addition to updating the `lean-toolchain` and `lakefile.lean`,
          in `.github/workflows/lean4checker.yml` update the line
          `git checkout v4.6.0` to the appropriate tag. 
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
- The `v4.6.0` section of `RELEASES.md` is out of sync between
  `releases/v4.6.0` and `master`. This should be reconciled:
  - Replace the `v4.6.0` section on `master` with the `v4.6.0` section on `releases/v4.6.0`
    and commit this to `master`.
- Merge the release announcement PR for the Lean website - it will be deployed automatically
- Finally, make an announcement!
  This should go in https://leanprover.zulipchat.com/#narrow/stream/113486-announce, with topic `v4.6.0`.
  Please see previous announcements for suggested language.
  You will want a few bullet points for main topics from the release notes.
  Link to the blog post from the Zulip announcement.
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
- We will rely on automatically generated release notes for release candidates,
  and the written release notes will be used for stable versions only.
  It is essential to choose the nightly that will become the release candidate as early as possible, to avoid confusion.
- In `src/CMakeLists.txt`,
  - verify that you see `set(LEAN_VERSION_MINOR 7)` (for whichever `7` is appropriate); this should already have been updated when the development cycle began.
  - `set(LEAN_VERSION_IS_RELEASE 1)` (this should be a change; on `master` and nightly releases it is always `0`).
  - Commit your changes to `src/CMakeLists.txt`, and push.
- `git tag v4.7.0-rc1`
- `git push origin v4.7.0-rc1`
- Ping the FRO Zulip that release notes need to be written. The release notes do not block completing the rest of this checklist.
- Now wait, while CI runs.
  - You can monitor this at `https://github.com/leanprover/lean4/actions/workflows/ci.yml`, looking for the `v4.7.0-rc1` tag.
  - This step can take up to an hour.
- (GitHub release notes) Once the release appears at https://github.com/leanprover/lean4/releases/
  - Verify that the release is marked as a prerelease (this should have been done automatically by the CI release job).
  - In the "previous tag" dropdown, select `v4.6.0`, and click "Generate release notes".
    This will add a list of all the commits since the last stable version.
    - Delete "update stage0" commits, and anything with a completely inscrutable commit message.
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
    It is essential for Mathlib CI that you then create the next `bump/v4.8.0` branch
    for the next development cycle.
    Set the `lean-toolchain` file on this branch to same `nightly` you used for this release.
  - For Batteries/Aesop/Mathlib, which maintain a `nightly-testing` branch, make sure there is a tag
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

We are currently trying a system where release notes are compiled all at once from someone looking through the commit history.
The exact steps are a work in progress.
Here is the general idea:

* The work is done right on the `releases/v4.6.0` branch sometime after it is created but before the stable release is made.
  The release notes for `v4.6.0` will later be copied to `master` when we begin a new development cycle.
* There can be material for release notes entries in commit messages.
* There can also be pre-written entries in `./releases_drafts`, which should be all incorporated in the release notes and then deleted from the branch.
  See `./releases_drafts/README.md` for more information.
* The release notes should be written from a downstream expert user's point of view.

This section will be updated when the next release notes are written (for `v4.10.0`).
