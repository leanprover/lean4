# Releasing Lean

The release process is driven by an interactive script at
`script/release/checklist.py`. When run without `-i/--interactive`, it's just an
automated checklist that reports the release's status. When run with
`-i/--interactive`, it also creates commits, tags, bump PRS, and updates the
release page itself. It will always wait for user consent before making any
modifications.

```
cd script/release
uv run checklist.py v4.X.Y -i
```

To perform a full release, you must be a member of the `lean-release-managers`
team in both `leanprover-community` and `leanprover`, as well as have write
access to the `fgdorais/lean4-unicode-basic` and `dupuisf/BibtexQuery` repos.

The `checklist.py` script does not fully automate the process. In some cases, it
will ask the user for manual intervention. Other areas that require manual
action are described in the sections below.

**You should double-check the script
outputs before choosing `Y` on prompts; manual intervention may be required
without the script noticing.** Details about each individual repository's
release process can be found in the comments in `script/release/repos.py`.

The script never merges PRs; you'll always have to do that manually. Sometimes,
manual intervention is required to make the PR mergeable. This often includes
merging the repo's nightly or bump branch into the PR. Further information can
be found in the comments in `script/release/repos.py`.

You should be able to ctrl+click any underlined parts of the script (assuming
your terminal emulator supports it) to open them in the browser.

## Release notes

The release notes live in the `leanprover/reference_manual` repository. In the
bump PR for a `v4.X.0-rc1` release, the release note page for `v4.X.0` is also
added to the reference manual. This not only adds a new file at
`Manual/Releases/v4_X_0.lean`, but also requires updates to imports in
`Manual/Releases.lean`. In later bump PRs, it is regenerated and updated using
the same script.

Before merging the release notes, check and potentially fix the verso warnings
in the release notes file.

At some point between the rc1 and the final release, a separate PR should be
opened to the reference manual containing release highlights. At the moment,
these highlights are generated using the `/release-highlights` claude skill and
then checked by at least one lean developer.

## Reference manual deployments

As described in the reference manual readme, the reference manual deploys
whenever one of its tags is pushed. You may need to force-push reference manual
tags after updating the release notes, e.g. after merging the release note
highlights PR.

## Release announcements

Once a version has been released, double check

1. whether the release page on GitHub has a description, release artifacts, and
   is tagged as pre-release if necessary,
2. whether the release notes have been deployed to the latest version of the
   reference manual, and
3. whether the toolchain can be used in elan.

If everything looks good, post an announcement of the release in the
corresponding channel in
<https://leanprover.zulipchat.com/#narrow/channel/579631-Lean-Releases>.

Announce stable releases on social media as well.

## Graphviz graphs

Both the `checklist.py` and the `repos.py` scripts have options to print a
graphviz dot graph of the different repos involved in the release process and
their dependencies. `checklist.py` includes the checklist status. Just chuck it
into a graphviz viewer of your choice, e.g.
<https://dreampuf.github.io/GraphvizOnline/>.
