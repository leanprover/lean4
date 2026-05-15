from argparse import ArgumentParser
from dataclasses import dataclass
from pathlib import Path

import repos
from github import Github, UnknownObjectException
from github.GitRef import GitRef
from rich import print
from rich.markup import escape as e

import util
from util import Checklist, CMakeVersion, ReleaseRepo, Version


@dataclass
class Config:
    version: Version
    interactive: bool
    skip_weak_deps: bool
    skip_mathlib_checks: bool
    github: Github


class RepoChecker:
    def __init__(self, config: Config, rrepo: ReleaseRepo) -> None:
        self.config = config
        self.cl = Checklist()

        self.rrepo = rrepo
        self.grepo = self.github.get_repo(self.rrepo.gh_full_name)
        self.lrepo = self.rrepo.local

    @property
    def github(self) -> Github:
        return self.config.github

    @property
    def version(self) -> Version:
        return self.config.version

    def prompt(self, message: str) -> bool:
        if not self.config.interactive:
            return False
        return util.prompt(message) == "y"

    def check_pr(self, base: str, head: str, title: str) -> bool:
        pr = util.find_pr(self.grepo, head=head, base=base, title=title)
        if not pr:
            if not self.prompt("PR not found. Create?"):
                self.cl.fatal("PR not found")
            return False

        if pr.state == "open":
            self.cl.blocked(f"PR open: {util.fmt_pr(pr)}")

        if pr.merged:
            self.cl.success(f"PR merged: {util.fmt_pr(pr)}")
        else:
            self.cl.success(f"PR closed: {util.fmt_pr(pr)}")

        return True

    def create_pr(
        self, base: str, head: str, title: str, nightly: ReleaseRepo | None = None
    ) -> None:
        if not self.prompt(f"Push branch [b]{e(head)}[/b]?"):
            self.cl.fatal("Branch not pushed")
        self.lrepo.push(head, remote="nightly" if nightly else "origin")

        # Mathlib bump PRs are opened from the nightly-testing repo, which
        # pygithub doesn't support because both belong to the same organization:
        # https://github.com/PyGithub/PyGithub/issues/2942
        # So we just give the user a link instead.
        if nightly:
            url = util.create_pr_url(
                base=self.rrepo,
                base_branch=base,
                head=nightly,
                head_branch=head,
                title=title,
            )
            self.cl.blocked(f"[u link={url}]Create PR manually[/]")

        if not self.prompt(f"Create PR for branch [b]{e(head)}[/b]?"):
            self.cl.fatal("PR not created")
        pr = util.create_pr(self.grepo, head=head, base=base, title=title)
        self.cl.blocked(f"PR created: {util.fmt_pr(pr)}")


class DownstreamChecker(RepoChecker):
    def check_dependencies_completed(self) -> None:
        deps = list(self.rrepo.strong_deps)
        if not self.config.skip_weak_deps:
            deps += self.rrepo.weak_deps
        for dep in deps:
            if not dep.completed:
                self.cl.wait(
                    f"Awaiting completion of dependency [b]{e(dep.gh_full_name)}[/b]"
                )
        self.cl.ensure_success()

    def check_toolchain(self) -> bool:
        expected = util.get_toolchain_for(self.version)
        actual = util.get_toolchain(self.grepo, self.grepo.default_branch)

        if expected == actual:
            self.cl.success(f"Toolchain is [b]{e(actual)}[/b]")
            return True
        else:
            self.cl.fail(f"Toolchain is [b]{e(actual)}[/b]")
            return False

    def _bump_toolchain(self, path: Path) -> None:
        util.set_toolchain(path, self.version.tag)

    def _bump_toolchain_deps(self, path: Path) -> None:
        if (path / "lakefile.toml").exists():
            util.edit(
                path / "lakefile.toml",
                r'rev = "v4\.[0-9]+(\.[0-9]+)?(-rc[0-9]+)?"',
                f'rev = "{self.version}"',
            )
        else:
            util.edit(
                path / "lakefile.lean",
                r'git "v4\.[0-9]+(\.[0-9]+)?(-rc[0-9]+)?"',
                f'git "{self.version}"',
            )

        util.run("lake", "update", cwd=path)

    def _bump_toolchain_mathlib4(self) -> None:
        pw = self.github.get_repo(repos.PROOFWIDGETS4.gh_full_name)
        tag = util.get_proofwidgets_release_for(pw, self.version)
        if not tag:
            raise SystemExit(1)

        # For both normal and rc1 PRs
        util.edit(
            self.lrepo.path / "lakefile.lean",
            r'"proofwidgets" @ git ".*"',
            f'"proofwidgets" @ git "{tag.name}"',
        )

        # For rc1 PRs
        util.edit(
            self.lrepo.path / "lakefile.lean",
            r' @ git "nightly-testing"',
            f' @ git "{self.version}"',
        )

        self._bump_toolchain_deps(self.lrepo.path)

    def _bump_toolchain_repl(self) -> None:
        self._bump_toolchain_deps(self.lrepo.path)

        mathlib = self.lrepo.path / "test" / "Mathlib"
        self._bump_toolchain(mathlib)
        self._bump_toolchain_deps(mathlib)

        if self.prompt("Run tests?"):
            try:
                util.run("./test.sh", cwd=self.lrepo.path)
                print("#####################")
                print("## Tests succeeded ##")
                print("#####################")
            except SystemExit as e:
                print("###################")
                print("## Tests failed! ##")
                print("###################")
                raise e

    def _bump_toolchain_verso(self) -> None:
        self._bump_toolchain_deps(self.lrepo.path)
        util.run("./update-subverso.sh", cwd=self.lrepo.path)

    def _bump_toolchain_reference_manual(self) -> None:
        self._bump_toolchain_deps(self.lrepo.path)

        if not self.prompt("Run release notes update script"):
            self.cl.fatal("Release notes update script not run")

        here = Path(__file__).parent
        util.run(
            "uv", "run", "release_notes.py", self.version.tag, self.lrepo.path, cwd=here
        )

        self.prompt("Check release notes before commit")

    def _bump_toolchain_lean_fro_org(self) -> None:
        self._bump_toolchain_deps(self.lrepo.path)

        hero = self.lrepo.path / "examples" / "hero"
        self._bump_toolchain(hero)
        self._bump_toolchain_deps(hero)

        util.run("scripts/update.sh", cwd=self.lrepo.path)

    def _bump_toolchain_bibtex_query(self) -> None:
        lub = self.github.get_repo(repos.LEAN4_UNICODE_BASIC.gh_full_name)
        tag = util.get_lean_unicode_basic_release_for(lub, self.version)
        rev = str(tag) if tag else "main"

        util.edit(
            self.lrepo.path / "lakefile.toml",
            r'(name = "UnicodeBasic"[\s\S]*?rev =) ".+?"',
            rf'\1 "{rev}"',
        )

        self._bump_toolchain_deps(self.lrepo.path)

    def _bump_toolchain_in_worktree(self) -> None:
        self._bump_toolchain(self.lrepo.path)

        # Special cases
        if self.rrepo.gh_full_name == repos.MATHLIB4.gh_full_name:
            self._bump_toolchain_mathlib4()
        elif self.rrepo.gh_full_name == repos.REPL.gh_full_name:
            self._bump_toolchain_repl()
        elif self.rrepo.gh_full_name == repos.VERSO.gh_full_name:
            self._bump_toolchain_verso()
        elif self.rrepo.gh_full_name == repos.REFERENCE_MANUAL.gh_full_name:
            self._bump_toolchain_reference_manual()
        elif self.rrepo.gh_full_name == repos.LEAN_FRO_ORG.gh_full_name:
            self._bump_toolchain_lean_fro_org()
        elif self.rrepo.gh_full_name == repos.BIBTEX_QUERY.gh_full_name:
            self._bump_toolchain_bibtex_query()
        elif self.rrepo.strong_deps:
            self._bump_toolchain_deps(self.lrepo.path)

    def _bump_toolchain_unicode_basic(self) -> None:
        base = self.grepo.default_branch
        head = f"update-toolchain-{self.version}"
        title = f"chore: update toolchain {self.version}"
        if self.check_pr(base=base, head=head, title=title):
            return

        workflow = self.grepo.get_workflow("update-toolchain.yml")
        for run in workflow.get_runs(branch=base).get_page(0):
            if not run.conclusion:
                what = f"[b u link={run.html_url}]Bump workflow run {run.id}[/]"
                self.cl.blocked(f"{what} is still running")
                return

        if not self.prompt("No PR or running bump workflow run found. Trigger?"):
            self.cl.fatal("No PR or running bump workflow run found")

        workflow.create_dispatch(ref=base)
        self.cl.blocked("Triggered bump workflow run")

    def check_bump_pr(self) -> None:
        if self.rrepo.gh_full_name == repos.LEAN4_UNICODE_BASIC.gh_full_name:
            self._bump_toolchain_unicode_basic()
            return

        # Normally:
        # 1. Create bump branch from origin/main
        # 2. Edit files 'n stuff and commit
        # 3. Push branch to origin
        # 4. Create PR to origin/main

        # Nightly:
        # 1. Create bump branch from origin/main
        # 2. Edit files 'n stuff and commit
        # 3. Push branch to nightly
        # 4. Create PR to origin/main

        # Normally, with RC1 and bump branch:
        # 1. Switch to origin/bump/v*
        # 2. Edit files 'n stuff and commit
        # 3. Push branch to origin
        # 4. Create PR to origin/main

        # Nightly, with RC1 and bump branch:
        # 1. Switch to nightly/bump/v*
        # 2. Edit files 'n stuff and commit
        # 3. Push branch to nightly
        # 4. Create PR to origin/main

        base = self.grepo.default_branch
        head = f"bump-to-{self.version}"
        nightly = None

        use_bump_branch = self.rrepo.bump_branch and self.version.rc == 1
        if use_bump_branch:
            head = util.get_bump_branch(self.version)
            nightly = self.rrepo.nightly

        title = util.get_toolchain_bump_message(self.version)
        if self.check_pr(base=base, head=head, title=title):
            return

        self.lrepo.prepare(nightly=nightly)
        if use_bump_branch:
            self.lrepo.switch(head, remote="nightly" if nightly else "origin")
        else:
            self.lrepo.create_branch(head)

        self._bump_toolchain_in_worktree()
        self.lrepo.commit(title)

        self.create_pr(base=base, head=head, title=title, nightly=nightly)

    def check_next_bump_branch(self) -> None:
        if not self.rrepo.bump_branch:
            return

        grepo = self.grepo
        if self.rrepo.nightly:
            grepo = self.github.get_repo(self.rrepo.nightly.gh_full_name)

        branch_name = util.get_bump_branch(self.version.next_minor)
        what = f"Bump branch [b]{e(branch_name)}[/b]"
        try:
            grepo.get_branch(branch_name)
            self.cl.success(f"{what} exists")
            return
        except UnknownObjectException:
            pass

        if not self.prompt(f"{what} not found. Create?"):
            self.cl.fail(f"{what} not found")
            return

        lean4_nightly = self.github.get_repo(repos.LEAN4_NIGHTLY.gh_full_name)
        latest_nightly_tag = util.get_latest_nightly_tag(lean4_nightly)

        self.lrepo.prepare(nightly=self.rrepo.nightly)
        self.lrepo.create_branch(branch_name)
        util.set_toolchain(self.lrepo.path, latest_nightly_tag.name)

        message = f"chore: bump toolchain to {latest_nightly_tag.name}"
        self.lrepo.commit(message)

        if not self.prompt(f"Push branch [b]{e(branch_name)}[/b]?"):
            self.cl.fail(f"{what} not found")
            return
        remote = "nightly" if self.rrepo.nightly else "origin"
        self.lrepo.push(branch_name, remote=remote)
        self.cl.success(f"{what} created")

    def _check_lean_release_tag(self) -> GitRef | None:
        tag_name = self.version.tag
        what = f"Toolchain tag [b]{tag_name}[/b]"

        try:
            tag = self.grepo.get_git_ref(f"tags/{tag_name}")
            self.cl.success(f"{what} exists")
            return tag
        except UnknownObjectException:
            pass

        if not self.prompt(f"{what} not found. Create?"):
            self.cl.fail(f"{what} not found")
            return

        self.lrepo.prepare()
        bump_sha = util.find_merged_toolchain_bump_sha(self.lrepo, self.version)
        self.lrepo.create_tag(tag_name, bump_sha)

        if not self.prompt(f"Push tag [b]{tag_name}[/b]?"):
            self.cl.fatal(f"{what} does not exist")
        self.lrepo.push(tag_name, upstream=False)

        tag = self.grepo.get_git_ref(f"tags/{tag_name}")
        self.cl.success(f"{what} created")
        return tag

    def _check_proofwidgets_release_tag(self) -> GitRef | None:
        what = f"Proofwidgets release with toolchain {self.version}"

        tag = util.get_proofwidgets_release_for(self.grepo, self.version)
        if tag:
            self.cl.success(f"{what} found: [b]{e(tag.name)}[/b]")
            return

        tag_name = util.get_next_proofwidgets_release(self.grepo)
        if not self.prompt(f"{what} not found. Create [b]{e(tag_name)}[/b]?"):
            self.cl.fail(f"{what} not found")
            return

        self.lrepo.prepare()
        bump_sha = util.find_merged_toolchain_bump_sha(self.lrepo, self.version)
        self.lrepo.create_tag(tag_name, bump_sha)

        if not self.prompt(f"Push tag [b]{tag_name}[/b]?"):
            self.cl.fatal(f"{what} does not exist")
        self.lrepo.push(tag_name, upstream=False)

        tag = self.grepo.get_git_ref(f"tags/{tag_name}")
        self.cl.success(f"{what} created")
        return tag

    def check_release_tag(self) -> GitRef | None:
        match self.rrepo.release_tag:
            case "lean":
                return self._check_lean_release_tag()
            case "proofwidgets":
                return self._check_proofwidgets_release_tag()
            case None:
                pass

    def check_stable_branch_points_to_release_tag(self, tag: GitRef) -> None:
        if not self.rrepo.stable_branch:
            return
        if not self.version.is_stable:
            return

        what = "Stable branch"

        branch = self.grepo.get_branch("stable")
        if branch.commit.sha == tag.object.sha:
            self.cl.success(f"{what} points to toolchain tag")
            return

        if not self.prompt(f"{what} does not point to toolchain tag. Update?"):
            self.cl.fail(f"{what} does not point to toolchain tag")
            return

        self.lrepo.prepare()
        self.lrepo.switch("stable")
        self.lrepo.git("merge", "--ff-only", self.version.tag)

        if not self.prompt("Push branch [b]stable[/b] to origin?"):
            self.cl.fail(f"{what} does not point to toolchain tag")
            return

        self.lrepo.push("stable")
        self.cl.success(f"{what} updated to point to toolchain tag")

    def check_mathlib4_version_tags(self) -> None:
        if self.rrepo.gh_full_name != repos.MATHLIB4.gh_full_name:
            return
        if self.config.skip_mathlib_checks:
            return

        # At this point, the PR has been merged
        self.lrepo.prepare()
        self.lrepo.switch(self.grepo.default_branch)

        script = "scripts/verify_version_tags.py"
        try:
            self.lrepo.run("python", script, self.version.tag)
            self.cl.success(f"Version tags verified by [b]{e(script)}[/b]")
        except Exception:
            self.cl.fatal(f"Version tag verification by [b]{e(script)}[/b] failed")

    def check(self) -> None:
        self.check_dependencies_completed()

        toolchain = self.check_toolchain()
        if not toolchain:
            self.check_bump_pr()
            self.cl.ensure_success()
        self.check_next_bump_branch()

        release_tag = self.check_release_tag()
        if release_tag:
            self.check_stable_branch_points_to_release_tag(release_tag)

        if toolchain:
            self.check_mathlib4_version_tags()

        self.cl.ensure_success()
        self.rrepo.completed = True


class LeanChecker(RepoChecker):
    def __init__(self, config: Config) -> None:
        super().__init__(config=config, rrepo=repos.LEAN4)

    def _check_label_exists(
        self, name: str, color: str, description: str | None = None
    ) -> None:
        what = f"Label [b]{e(name)}[/b]"

        try:
            self.grepo.get_label(name)
            self.cl.success(f"{what} exists")
            return
        except UnknownObjectException:
            pass

        if not self.prompt(f"{what} does not exist. Create?"):
            self.cl.fail(f"{what} does not exist")
            return

        if description is None:
            self.grepo.create_label(name=name, color=color)
        else:
            self.grepo.create_label(name=name, color=color, description=description)
        self.cl.success(f"{what} created")

    def check_backport_label_exists(self, version: Version) -> None:
        self._check_label_exists(
            name=util.get_backport_label(version),
            color="1d76db",
        )

    def check_blocking_label_exists(self, version: Version) -> None:
        self._check_label_exists(
            name=util.get_blocking_label(version),
            color="b60205",
            description=f"Blocks the next {version.base} release candidate or release from being published.",
        )

    def check_release_branch_exists(self) -> None:
        branch_name = util.get_releases_branch(self.version)
        what = f"Release branch [b]{e(branch_name)}[/b]"

        try:
            self.grepo.get_branch(branch_name)
            self.cl.success(f"{what} exists")
            return
        except UnknownObjectException:
            pass

        if not self.prompt(f"{what} does not exist. Create?"):
            self.cl.fatal(f"{what} does not exist")

        self.lrepo.prepare()
        self.lrepo.create_branch(branch_name)

        if not self.prompt(f"Push branch [b]{e(branch_name)}[/b]?"):
            self.cl.fatal(f"{what} does not exist")
        self.lrepo.push(branch_name)

        self.grepo.get_branch(branch_name)
        self.cl.success(f"{what} created")

    def check_release_branch_cmake_version(self) -> None:
        branch_name = util.get_releases_branch(self.version)
        what = f"CMake version settings on [b]{e(branch_name)}[/b]"
        target = CMakeVersion(self.version.stable, is_release=True)

        cur = util.get_cmake_version(self.grepo, branch_name)
        if cur == target:
            self.cl.success(f"{what} are correct")
            return

        if not self.prompt(f"{what} are incorrect. Update?"):
            self.cl.fail(f"{what} are incorrect")
            return

        self.lrepo.prepare()
        self.lrepo.switch(branch_name)
        util.set_cmake_version(self.lrepo, target)
        self.lrepo.commit("chore: prepare release")

        if not self.prompt(f"Push branch [b]{e(branch_name)}[/b]?"):
            self.cl.fail(f"{what} are incorrect")
            return
        self.lrepo.push(branch_name)
        self.cl.success(f"{what} updated")

    def check_master_branch_cmake_version(self) -> None:
        branch_name = self.grepo.default_branch
        what = f"CMake version settings on [b]{e(branch_name)}[/b]"
        target = CMakeVersion(self.version.next_minor, is_release=False)

        cur = util.get_cmake_version(self.grepo, branch_name)
        if cur == target:
            self.cl.success(f"{what} are correct")
            return
        self.cl.fail(f"{what} are incorrect")

        head = f"dev-cycle-{self.version.next_minor}"
        title = f"chore: prepare development cycle for {self.version.next_minor}"
        if self.check_pr(base=branch_name, head=head, title=title):
            return

        self.lrepo.prepare()
        self.lrepo.create_branch(head, branch_name)
        util.set_cmake_version(self.lrepo, target)
        self.lrepo.commit(title)

        self.create_pr(base=branch_name, head=head, title=title)

    def _check_no_open_prs_labeled(self, label: str) -> None:
        success = True
        for issue in self.grepo.get_issues(state="open", labels=[label]):
            kind = "PR" if issue.pull_request else "issue"
            self.cl.fail(f"Found {kind} {util.fmt_pr(issue)} labeled [b]{e(label)}[/b]")
            success = False
        if success:
            self.cl.success(f"Found no open PRs labeled [b]{e(label)}[/b]")

    def check_no_open_prs_labeled_backport(self) -> None:
        self._check_no_open_prs_labeled(util.get_backport_label(self.version))

    def check_no_open_prs_labeled_blocking(self) -> None:
        self._check_no_open_prs_labeled(util.get_blocking_label(self.version))

    def check_no_open_backport_prs(self) -> None:
        base = util.get_releases_branch(self.version)
        success = True
        for pr in self.grepo.get_pulls(state="open", base=base):
            if "backport" in pr.title.lower():
                self.cl.fail(f"Found backport PR #{pr.number} {util.fmt_pr(pr)}")
                success = False
        if success:
            self.cl.success("Found no open backport PRs")

    def check_release_tag(self) -> GitRef:
        tag_name = self.version.tag
        what = f"Tag [b]{tag_name}[/b]"

        try:
            ref = self.grepo.get_git_ref(f"tags/{tag_name}")
            self.cl.success(f"{what} exists")
            return ref
        except UnknownObjectException:
            pass

        if not self.prompt(f"{what} does not exist. Create?"):
            self.cl.fatal(f"{what} does not exist")

        self.lrepo.prepare()
        self.lrepo.create_tag(tag_name, util.get_releases_branch(self.version))

        if not self.prompt(f"Push tag [b]{tag_name}[/b]?"):
            self.cl.fatal(f"{what} does not exist")
        self.lrepo.push(tag_name, upstream=False)

        tag = self.grepo.get_git_ref(f"tags/{tag_name}")
        self.cl.success(f"{what} created")
        return tag

    def check_release_ci(self, release_tag: GitRef) -> None:
        tag_sha = release_tag.object.sha
        runs = self.grepo.get_workflow_runs(event="push", head_sha=tag_sha).get_page(0)
        if len(runs) == 0:
            self.cl.fail("Release workflow run not found")
            return

        run = runs[0]
        what = f"[b u link={run.html_url}]Release workflow run {run.id}[/]"

        if not run.conclusion:
            self.cl.blocked(f"{what} is still running")
        if run.conclusion != "success":
            self.cl.fatal(f"{what} failed")
        self.cl.success(f"{what} finished")

    def check_release_page(self) -> None:
        url = f"https://github.com/leanprover/lean4/releases/tag/{self.version}"
        what = f"[b u link={url}]Release page for {self.version.tag}[/]"
        try:
            release = self.grepo.get_release(self.version.tag)
        except UnknownObjectException:
            self.cl.blocked(f"{what} not found")

        target = "This is"
        if not self.version.is_stable:
            target += f" release candidate {self.version.rc} for"
        target += f" the {self.version.stable} release of Lean."
        relnotes = f"https://lean-lang.org/doc/reference/latest/releases/{self.version.stable}/"
        target += f" View the [release notes]({relnotes}) for more information."

        incorrect = []
        if release.name != str(self.version):
            incorrect.append("name")
        if release.body is None or release.body.strip() != target:
            incorrect.append("message")
        if not incorrect:
            self.cl.success(f"{what} exists")
            return

        if not self.prompt(f"{what} has incorrect {'/'.join(incorrect)}. Update?"):
            self.cl.fail(f"{what} has incorrect {'/'.join(incorrect)}")
            return

        release.update_release(
            name=str(self.version),
            message=target,
            prerelease=not self.version.is_stable,
        )
        self.cl.success(f"{what} updated")

    def check(self) -> None:
        self.cl.section("Prepare release cycle")
        self.check_backport_label_exists(self.version)
        self.check_blocking_label_exists(self.version)
        self.check_blocking_label_exists(self.version.next_minor)
        self.check_release_branch_exists()
        self.check_release_branch_cmake_version()
        self.check_master_branch_cmake_version()

        self.cl.section("Release")
        self.check_no_open_prs_labeled_backport()
        self.check_no_open_prs_labeled_blocking()
        self.check_no_open_backport_prs()
        release_tag = self.check_release_tag()
        self.check_release_ci(release_tag)
        self.check_release_page()

        for drepo in repos.ALL:
            self.cl.section(f"[u link={drepo.gh_url}]{e(drepo.gh_full_name)}[/u link]")
            try:
                DownstreamChecker(config=self.config, rrepo=drepo).check()
            except SystemExit:
                self.cl.failed = True

        self.cl.ensure_success()


class Args:
    version: Version
    interactive: bool
    skip_weak_deps: bool
    skip_mathlib_checks: bool
    graph: bool


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("version", type=Version.parse)
    parser.add_argument("-i", "--interactive", action="store_true")
    parser.add_argument("-W", "--skip-weak-deps", action="store_true")
    parser.add_argument("-M", "--skip-mathlib-checks", action="store_true")
    parser.add_argument("-g", "--graph", action="store_true")
    args = parser.parse_args(namespace=Args())

    util.initialize_rich()
    github = util.get_github_instance()
    config = Config(
        version=args.version,
        interactive=args.interactive,
        skip_weak_deps=args.skip_weak_deps,
        skip_mathlib_checks=args.skip_mathlib_checks,
        github=github,
    )

    try:
        LeanChecker(config=config).check()
    finally:
        if args.graph:
            print()
            repos.print_graphviz_dot()
