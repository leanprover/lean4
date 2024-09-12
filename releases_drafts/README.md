Draft release notes
-------------------

This folder contains drafts of release notes for inclusion in `RELEASES.md`.
During the process to create a release candidate, we look through all the commits that make up the release
to prepare the release notes, and in that process we take these drafts into account.

Guidelines:
- You should prefer adding release notes to commit messages over adding anything to this folder.
  A release note should briefly explain the impact of a change from a user's point of view.
  Please mark these parts out with words such as **release notes** and/or **breaking changes**.
- It is not necessary to add anything to this folder. It is meant for larger features that span multiple PRs,
  or for anything that would be helpful when preparing the release notes that might be missed
  by someone reading through the change log.
- If the PR that adds a feature simultaneously adds a draft release note, including the PR number is not required
  since it can be obtained from the git history for the file.

When release notes are prepared, all the draft release notes are deleted from this folder.
For release candidates beyond the first one, you can either update `RELEASE.md` directly
or continue to add drafts.

When a release is finalized, we will copy the completed release notes from `RELEASE.md` to the `master` branch.
