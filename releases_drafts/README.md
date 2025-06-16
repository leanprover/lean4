Draft release notes
-------------------

This folder contains drafts of release notes for the upcoming version.
During the process to create a release candidate, we look through all the commits that make up the release
to prepare the release notes, and in that process we take these drafts into account.

Guidelines:
- Write good commit messages
  The first paragraph should briefly explain the impact of a change from a user's point of view.
  (Recall: the first paragraph, which should begin with "This PR",
  is automatically incorporated into the release notes by `script/release_notes.py`.
  See `doc/dev/release_checklist.md` for more details.).
- This folder is only needed for larger features that span multiple PRs,
  or for anything that would be helpful when preparing the release notes that might be missed
  by someone reading through the change log.

When notes from this folder are incorporated into the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/releases/#release-notes),
they should then be deleted from here.
