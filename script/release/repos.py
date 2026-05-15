from argparse import ArgumentParser

from util import ReleaseRepo

ALL: list[ReleaseRepo] = []
BY_FULL_NAME: dict[str, ReleaseRepo] = {}


def _register(repo: ReleaseRepo) -> None:
    ALL.append(repo)
    BY_FULL_NAME[repo.gh_full_name] = repo


##################
## Repositories ##
##################


# Repositories managed by this release process should specify their dependencies
# through reservoir name/scope. The versions should be specified via tags, where
# available, or commit hashes otherwise.


# For release `v4.X.0-rc1`, a branch `releases/v4.X.0` is created off of
# `master`. This branch is reused for all subsequent release candidates and
# releases with the same major and minor version, e.g. `v4.X.0`, `v4.X.1`.
#
# `src/CMakeLists.txt` contains the variables LEAN_VERSION_MAJOR,
# LEAN_VERSION_MINOR, LEAN_VERSION_PATCH, and LEAN_VERSION_IS_RELEASE. On
# master, these should point to the next release once the release branch is cut,
# i.e. `v4.X+1.0`, and LEAN_VERSION_IS_RELEASE should be 0. On the release
# branch, these should point to the current release (and updated only when
# necessary for patch releases), and LEAN_VERSION_IS_RELEASE should be 1.
#
# Before creating a release, ensure that no blocking issues/PRs or open backport
# PRs exist. See also the labels `backport releases/v4.X.0` and
# `blocks-release-v4.X.0` on GitHub. There should also be a
# `blocks-release-v4.X+1.0` label corresponding to the CMakeLists version on
# `master`, which should be created after cutting a release branch.
#
# To create a release, push a tag `v4.X.Y` or `v4.X.Y-rcZ`. The tag triggers CI,
# which builds the release artifacts and creates a release on GitHub.
#
# After a release has been created, its description may need to be updated. For
# release candidates, it should read "This is the n-th release candidate for the
# v4.X.Y release of Lean." For releases, it should read "This is the v4.X.Y
# release of Lean. View the release notes for more information." where "release
# notes" is a link to the corresponding release notes section. If the release
# notes has not yet been updated, this second sentence can be omitted and added
# later.
#
# Finally, all the other repos listed below should be updated to use the newly
# released version of Lean.
LEAN4 = ReleaseRepo(github=("leanprover", "lean4"))
# Don't register this repo!

LEAN4_NIGHTLY = ReleaseRepo(github=("leanprover", "lean4-nightly"))
# Don't register this repo!


# To create a new release, open a PR into `main`. In it, bump the toolchain.
#
# For `v4.X.0-rc1` releases, use the existing `bump/v4.X.0` branch. To get the
# latest nightly fixes, you may need to merge the latest
# `bump/nightly-YYYY-MM-DD` PRs, or merge `nightly-testing` directly. After
# merging the PR, create a new `bump/v4.X+1.0` branch off of `main`.
#
# For other releases, create a new branch off of `main` and use it for the PR.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
# Then, update the `stable` branch to point to the same commit.
BATTERIES = ReleaseRepo(
    github=("leanprover-community", "batteries"),
    bump_branch=True,
    release_tag="lean",
    stable_branch="stable",
)
_register(BATTERIES)


# To create a new release, open a PR into `master`. In it, bump the toolchain
# and all dependencies. For `v4.X.0-rc1` releases, you may need to merge
# `nightly-testing` into the PR.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
# Then, update the `stable` branch to point to the same commit.
AESOP = ReleaseRepo(
    github=("leanprover-community", "aesop"),
    release_tag="lean",
    stable_branch="stable",
    strong_deps=[BATTERIES],
)
_register(AESOP)


# To create a new release, open a PR into `main`. In it, bump the toolchain and
# all dependencies. For `v4.X.0-rc1` releases, you may need to merge
# `nightly-testing` into the PR.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
LEAN4_CLI = ReleaseRepo(
    github=("leanprover", "lean4-cli"),
    release_tag="lean",
)
_register(LEAN4_CLI)


# To create a new release, open a PR into `main`. In it, bump the toolchain and
# all dependencies. For `v4.X.0-rc1` releases, you may need to merge
# `nightly-testing` into the PR.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
IMPORT_GRAPH = ReleaseRepo(
    github=("leanprover-community", "import-graph"),
    release_tag="lean",
    strong_deps=[LEAN4_CLI],
)
_register(IMPORT_GRAPH)


# To create a new release, open a PR into `main`. In it, bump the toolchain. For
# `v4.X.0-rc1` releases, you may need to merge `nightly-testing` into the PR.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
PLAUSIBLE = ReleaseRepo(
    github=("leanprover-community", "plausible"),
    release_tag="lean",
)
_register(PLAUSIBLE)


# To create a new release, open a PR into `main`. In it, bump the toolchain. For
# `v4.X.0-rc1` releases, you may need to merge `nightly-testing` into the PR.
#
# Obtain the next ProofWidgets version number by incrementing the patch version
# of the latest release (which will have the form `v0.0.X`). Once the release PR
# is merged, tag the resulting commit with the new version number.
PROOFWIDGETS4 = ReleaseRepo(
    github=("leanprover-community", "ProofWidgets4"),
    release_tag="proofwidgets",
)
_register(PROOFWIDGETS4)

# To create a new release, open a PR into `main`. In it, bump the toolchain. For
# `v4.X.0-rc1` releases, you may need to merge `nightly-testing` into the PR.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
# Then, update the `stable` branch to point to the same commit.
QUOTE4 = ReleaseRepo(
    github=("leanprover-community", "quote4"),
    release_tag="lean",
    stable_branch="stable",
)
_register(QUOTE4)


# To create a new release, open a PR into `master`. In it, bump the toolchain
# and all dependencies.
#
# For `v4.X.0-rc1` releases, use the existing `bump/v4.X.0` branch from the
# nightly repo. To get the latest nightly fixes, you may need to merge the
# latest `bump/nightly-YYYY-MM-DD` PRs, or merge `nightly-testing` directly.
# After merging the PR, create a new `bump/v4.X+1.0` branch off of `master`.
#
# For other releases, create a new branch off of `master` and use it for the PR.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
# Then, update the `stable` branch to point to the same commit.
MATHLIB4 = ReleaseRepo(
    github=("leanprover-community", "mathlib4"),
    nightly=ReleaseRepo(github=("leanprover-community", "mathlib4-nightly-testing")),
    bump_branch=True,
    release_tag="lean",
    stable_branch="stable",
    strong_deps=[BATTERIES, QUOTE4, AESOP, PROOFWIDGETS4, IMPORT_GRAPH, PLAUSIBLE],
)
_register(MATHLIB4)


# To create a new release, open a PR into `main`. In it, bump the toolchain and
# all dependencies.
#
# For `v4.X.0-rc1` releases, use the existing `bump/v4.X.0` branch. To get the
# latest nightly fixes, you may need to merge the latest
# `bump/nightly-YYYY-MM-DD` PRs, or merge `nightly-testing` directly. After
# merging the PR, create a new `bump/v4.X+1.0` branch off of `main`.
#
# For other releases, create a new branch off of `main` and use it for the PR.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
# Then, update the `stable` branch to point to the same commit.
CSLIB = ReleaseRepo(
    github=("leanprover", "cslib"),
    bump_branch=True,
    release_tag="lean",
    stable_branch="stable",
    strong_deps=[MATHLIB4],
)
_register(CSLIB)


# To create a new release, open a PR into `main`. In it, bump the toolchain and
# all dependencies. Also bump the toolchain and deps in `test/Mathlib`. Maybe
# run the tests locally before creating the PR? For `v4.X.0-rc1` releases, you
# may need to merge `nightly-testing` into the PR.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
# Then, update the `stable` branch to point to the same commit.
REPL = ReleaseRepo(
    github=("leanprover-community", "repl"),
    release_tag="lean",
    stable_branch="stable",
    strong_deps=[MATHLIB4],  # For tests in CI
)
_register(REPL)


# To create a new release, open a PR into `main`. In it, bump the toolchain and
# all dependencies, then run `update-subverso.sh`. For `v4.X.0-rc1` releases,
# you may need to merge `nightly-testing` into the PR.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
VERSO = ReleaseRepo(
    github=("leanprover", "verso"),
    release_tag="lean",
    strong_deps=[PLAUSIBLE],
    weak_deps=[MATHLIB4],  # For benchmarks
)
_register(VERSO)

# To create a new release, open a PR into `main`. In it, bump the toolchain and
# all dependencies. For `v4.X.0-rc1` releases, you may need to merge
# `nightly-testing` into the PR.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
VERSO_WEB_COMPONENTS = ReleaseRepo(
    github=("leanprover", "verso-web-components"),
    release_tag="lean",
    strong_deps=[VERSO],
)
_register(VERSO_WEB_COMPONENTS)


# To bump the toolchain, open a PR into `main`. In it, bump the toolchain and
# all dependencies.
#
# For `v4.X.0-rc1` releases, generate a new set of release notes and ensure
# they're imported and linked. For other releases, regenerate the existing
# release notes. For `v4.X.0-rc1` releases, you may also need to merge
# `nightly-testing` into the PR.
#
# Once the toolchain bump PR is merged, tag the resulting commit with the lean
# version. If the tag already exists, it may need to be updated manually.
#
# Highlights should be added in a separate PR and merged only shortly before the
# final release. That way, they don't get in the way of the RC bumps and can be
# commented on by the other developers.
REFERENCE_MANUAL = ReleaseRepo(
    github=("leanprover", "reference-manual"),
    release_tag="lean",
    strong_deps=[VERSO_WEB_COMPONENTS, VERSO],
)
_register(REFERENCE_MANUAL)


# To create a new release, open a PR into `main`. In it, bump the toolchain and
# all dependencies. Also bump the toolchain and dependencies in `examples/hero`.
# Finally, run `scripts/update.sh`. For `v4.X.0-rc1` releases, you may need to
# merge `nightly-testing` into the PR.
LEAN_FRO_ORG = ReleaseRepo(
    github=("leanprover", "lean-fro.org"),
    strong_deps=[VERSO, VERSO_WEB_COMPONENTS],
)
_register(LEAN_FRO_ORG)


# To create a new release, trigger the "Update Toolchain" CI workflow and wait
# for it to open a PR, then merge the PR if it looks good. For non-RC releases,
# wait for the maintainer to release a new version.
LEAN4_UNICODE_BASIC = ReleaseRepo(
    github=("fgdorais", "lean4-unicode-basic"),
)
_register(LEAN4_UNICODE_BASIC)


# To create a new release, open a PR into `master`. In it, bump the toolchain
# and all dependencies. For `v4.X.0-rc1` releases, you may need to merge
# `nightly-testing` into the PR.
BIBTEX_QUERY = ReleaseRepo(
    github=("dupuisf", "BibtexQuery"),
    release_tag="lean",
    strong_deps=[LEAN4_UNICODE_BASIC],
)
_register(BIBTEX_QUERY)

# To create a new release, open a PR into `master`. In it, bump the toolchain
# and all dependencies.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
LEANSQLITE = ReleaseRepo(
    github=("leanprover", "leansqlite"),
    release_tag="lean",
    strong_deps=[PLAUSIBLE],
)
_register(LEANSQLITE)

# To create a new release, open a PR into `main`. In it, bump the toolchain and
# all dependencies. For `v4.X.0-rc1` releases, you may need to merge
# `nightly-testing` into the PR.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
DOC_GEN4 = ReleaseRepo(
    github=("leanprover", "doc-gen4"),
    release_tag="lean",
    strong_deps=[BIBTEX_QUERY, LEAN4_UNICODE_BASIC, LEAN4_CLI, LEANSQLITE],
    # Doc-gen4 shouldn't lag behind mathlib if possible because of downstream
    # users, and doc-gen4 benchmarks failing for a short while is an acceptable
    # price to pay for that.
    # https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Tagging.20commits.20in.20mathlib4/near/585725955
    ignored_deps=[MATHLIB4],  # For benchmarks
)
_register(DOC_GEN4)
BATTERIES.ignored_deps.append(DOC_GEN4)


# To create a new release, open a PR into `master`. In it, bump the toolchain
# and all dependencies.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
COMPARATOR = ReleaseRepo(
    github=("leanprover", "comparator"),
    release_tag="lean",
)
_register(COMPARATOR)


# To create a new release, open a PR into `master`. In it, bump the toolchain
# and all dependencies.
#
# Once the release PR is merged, tag the resulting commit with the lean version.
LEAN4EXPORT = ReleaseRepo(
    github=("leanprover", "lean4export"),
    release_tag="lean",
)
_register(LEAN4EXPORT)


###################
## Visualization ##
###################


def transitive_strong_deps(repo: ReleaseRepo) -> set[str]:
    result = set()
    for dep in repo.strong_deps:
        result.add(dep.gh_full_name)
        result |= transitive_strong_deps(dep)
    return result


def indirect_strong_deps(repo: ReleaseRepo) -> set[str]:
    result = set()
    for dep in repo.strong_deps:
        result |= transitive_strong_deps(dep)
    return result


def graphviz_attrs(**kwargs: str) -> str:
    if not kwargs:
        return ""
    style_str = " ".join(f"{k}=<{v}>" for k, v in kwargs.items())
    return f" [{style_str}]"


def print_graphviz_line(
    repo: ReleaseRepo,
    dep: ReleaseRepo,
    comment: bool = False,
    attrs: dict[str, str] | None = None,
) -> None:
    comment_str = "// " if comment else ""
    attrs_str = graphviz_attrs(**attrs or {})
    print(f'  {comment_str}"{dep.gh_full_name}" -> "{repo.gh_full_name}"{attrs_str};')


def print_graphviz_dot(
    prune: bool = True, no_weak: bool = False, no_ignored: bool = False
) -> None:
    print("digraph G {")
    print("  rankdir=LR;")

    for repo in sorted(ALL, key=lambda r: r.gh_full_name):
        indirect = indirect_strong_deps(repo)

        # label = f"<FONT POINT_SIZE=10>{repo.gh_owner}</FONT>{repo.gh_name}"
        label = f'<FONT POINT-SIZE="8">{repo.gh_owner}</FONT><BR/>{repo.gh_name}'
        attrs = {"label": label}
        if repo.completed:
            attrs["style"] = "filled"
            attrs["color"] = "palegreen"
        print(f'  "{repo.gh_full_name}"{graphviz_attrs(**attrs)};')

        for dep in repo.strong_deps:
            comment = prune and dep.gh_full_name in indirect
            print_graphviz_line(repo, dep, comment=comment)
        for dep in repo.weak_deps:
            comment = no_weak or (prune and dep.gh_full_name in indirect)
            print_graphviz_line(repo, dep, comment=comment, attrs={"style": "dashed"})
        for dep in repo.ignored_deps:
            comment = no_ignored or (prune and dep.gh_full_name in indirect)
            attrs = {"style": "dashed", "color": "red", "constraint": "false"}
            print_graphviz_line(repo, dep, comment=comment, attrs=attrs)

    print("}")


def print_all_urls() -> None:
    for repo in ALL:
        print(f"- {repo.gh_url}")


def clone_all_repos() -> None:
    for repo in ALL:
        print(f"Cloning {repo.gh_full_name}...")
        repo.local.prepare()


class Args:
    graph: bool
    prune: bool
    no_weak: bool
    no_ignored: bool
    urls: bool
    clone: bool


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("-g", "--graph", action="store_true")
    parser.add_argument("-p", "--prune", action="store_true")
    parser.add_argument("-W", "--no-weak", action="store_true")
    parser.add_argument("-I", "--no-ignored", action="store_true")
    parser.add_argument("-u", "--urls", action="store_true")
    parser.add_argument("-c", "--clone", action="store_true")
    args = parser.parse_args(namespace=Args())

    if args.graph:
        print_graphviz_dot(
            prune=args.prune, no_weak=args.no_weak, no_ignored=args.no_ignored
        )

    if args.urls:
        print_all_urls()

    if args.clone:
        clone_all_repos()
