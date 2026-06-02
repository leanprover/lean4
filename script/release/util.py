import datetime
import re
import shlex
import subprocess
import urllib.parse
from dataclasses import dataclass, field
from os import PathLike
from pathlib import Path
from re import Match, Pattern
from typing import Callable, Literal, NoReturn, Self

from github import Auth, Github
from github.GithubException import UnknownObjectException
from github.GitRelease import GitRelease
from github.Issue import Issue
from github.PullRequest import PullRequest
from github.Repository import Repository
from github.Tag import Tag
from rich import get_console, print, reconfigure
from rich.markup import escape as e

type Arg = str | bytes | PathLike[str] | PathLike[bytes]


def run(*args: Arg, cwd: Path | None = None, silent: bool = False) -> None:
    print(f"[bright_black]$ {e(' '.join(shlex.quote(str(arg)) for arg in args))}[/]")
    subprocess.run(args, check=True, cwd=cwd, capture_output=silent)


def run_stdout(*args: Arg, cwd: Path | None = None) -> str:
    print(f"[bright_black]$ {e(' '.join(shlex.quote(str(arg)) for arg in args))}[/]")
    return subprocess.run(
        args,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
        cwd=cwd,
    ).stdout


def prompt(message: str, options: str = "Yn") -> str:
    default: str | None = None
    for c in options:
        if c.isupper():
            default = c.lower()
            break

    options = options.lower()
    options_display = "/".join(c.upper() if c == default else c for c in options)

    console = get_console()
    while True:
        response = (
            console.input(f"{message} [cyan]\\[{options_display}]:[/] ").strip().lower()
        )
        if not response and default:
            return default
        elif response in options.lower():
            return response
        else:
            print(f"Please enter {options_display}.")


@dataclass
class Version:
    major: int
    minor: int
    patch: int
    rc: int | None = None

    @classmethod
    def parse(cls, s: str) -> Self:
        m = re.fullmatch(r"v(\d+)\.(\d+)\.(\d+)(-rc(\d+))?", s)
        if m is None:
            raise ValueError(f"Invalid version string: {s!r}")
        return cls(
            major=int(m.group(1)),
            minor=int(m.group(2)),
            patch=int(m.group(3)),
            rc=int(m.group(5)) if m.group(4) else None,
        )

    @property
    def raw(self) -> str:
        main = f"{self.major}.{self.minor}.{self.patch}"
        rc = "" if self.rc is None else f"-rc{self.rc}"
        return main + rc

    @property
    def tag(self) -> str:
        return f"v{self.raw}"

    @property
    def base(self) -> Self:
        return Version(major=self.major, minor=self.minor, patch=0, rc=None)

    @property
    def next_minor(self) -> Self:
        return Version(major=self.major, minor=self.minor + 1, patch=0, rc=None)

    @property
    def prev(self) -> Self:
        if self.patch > 0:
            return Version(major=self.major, minor=self.minor, patch=self.patch - 1)
        return Version(major=self.major, minor=self.minor - 1, patch=0)

    @property
    def stable(self) -> Self:
        return Version(major=self.major, minor=self.minor, patch=self.patch, rc=None)

    @property
    def is_stable(self) -> bool:
        return self.rc is None

    def __str__(self) -> str:
        return self.tag


@dataclass
class ReleaseRepo:
    github: tuple[str, str]  # (owner, name)

    # If present, nightly-related branches and tags are expected to be in this
    # repo instead of the main repo.
    nightly: Self | None = None

    # Use "bump/v4.X.0" branches for rc1 releases. Respect `nightly` if set.
    bump_branch: bool = False

    # When set, the version bump commit should be tagged. When set to "lean",
    # use the lean version tag as release tag. When set to "proofwidgets", use
    # proofwidgets versioning logic.
    release_tag: Literal["lean", "proofwidgets"] | None = None

    # When set, this branch should be updated to point to the version bump commit.
    stable_branch: str | None = None

    # Strong deps are dependencies that *must* be updated before a new version
    # of the repo can be released. Strong deps include all dependencies
    # specified in the lakefile, as well as those used by CI involved in merging
    # PRs or creating releases.
    strong_deps: list[Self] = field(default_factory=list)

    # Weak deps are indirect dependencies that are not strictly required to
    # create a new release, but make life easier if they're respected. For
    # example, this includes dependencies in parts of the CI that are not
    # related to releases, or dependencies used during benchmarking.
    #
    # These dependencies should be safe to ignore when time-critical.
    weak_deps: list[Self] = field(default_factory=list)

    # Ignored deps are weak deps that are intentionally ignored, e.g. to prevent
    # dependency cycles.
    ignored_deps: list[Self] = field(default_factory=list)

    # Mutable
    completed: bool = False

    @property
    def gh_owner(self) -> str:
        return self.github[0]

    @property
    def gh_name(self) -> str:
        return self.github[1]

    @property
    def gh_full_name(self) -> str:
        return "/".join(self.github)

    @property
    def gh_url(self) -> str:
        return f"https://github.com/{self.gh_full_name}"

    @property
    def local(self) -> "LocalRepo":
        path = Path(__file__).parent.parent.parent.parent / "release" / self.gh_name
        return LocalRepo(rrepo=self, path=path)


@dataclass
class LocalRepo:
    rrepo: ReleaseRepo
    path: Path

    def run(self, *args: Arg, silent: bool = False) -> None:
        run(*args, cwd=self.path, silent=silent)

    def run_stdout(self, *args: Arg) -> str:
        return run_stdout(*args, cwd=self.path)

    def git(self, *args: Arg, silent: bool = False) -> None:
        self.run("git", *args, silent=silent)

    def git_stdout(self, *args: Arg) -> str:
        return self.run_stdout("git", *args)

    def _prepare_remotes(self, nightly: ReleaseRepo | None) -> None:
        target = {"origin": self.rrepo}
        if nightly:
            target["nightly"] = nightly

        actual = {r.strip() for r in self.git_stdout("remote").splitlines()}

        for remote in actual - target.keys():
            self.git("remote", "remove", remote)

        for name, repo in target.items():
            url = f"git@github.com:{repo.gh_full_name}.git"
            if name in actual:
                self.git("remote", "set-url", name, url)
            else:
                self.git("remote", "add", name, url)

    def prepare(self, nightly: ReleaseRepo | None = None) -> None:
        # Clone
        if not self.path.exists():
            run("gh", "repo", "clone", self.rrepo.gh_full_name, self.path)

        self._prepare_remotes(nightly)

        # Check worktree is ready
        self.git("diff", "--quiet")
        self.git("clean", "-dffx", silent=True)

        # Fetch recent changes
        self.git("fetch", "--all", "--prune", "--prune-tags", "--force", silent=True)
        if nightly:  # Some tags may have been pruned away
            self.git("fetch", "--all", "--prune", silent=True)

    def switch(self, branch: str, remote: str = "origin") -> None:
        self.git("switch", "-C", branch, f"{remote}/{branch}")

    def create_branch(
        self, branch: str, remote: str = "origin", remote_branch: str | None = None
    ) -> None:
        if remote_branch is None:
            self.git("switch", "-C", branch, remote)  # Default branch
        else:
            self.git("switch", "-C", branch, f"{remote}/{remote_branch}")

    def create_tag(self, tag: str, target: str) -> None:
        self.git("tag", "-f", tag, target)

    def commit(self, message: str) -> None:
        self.git("add", ".")
        try:
            self.git("diff", "--cached", "--quiet")
        except Exception:
            self.git("commit", "-m", message)

    def push(self, branch: str, remote: str = "origin", upstream: bool = True) -> None:
        if upstream:
            self.git("push", "-u", remote, branch, silent=True)
        else:
            self.git("push", remote, branch, silent=True)


class Checklist:
    def __init__(self) -> None:
        self.failed = False

    def section(self, *message: str) -> None:
        print()
        print(f"[bold]{''.join(message)}[/]")

    def success(self, *message: str) -> None:
        print(f"[b green]\\[Y][/] {''.join(message)}")

    def warn(self, *message: str) -> None:
        print(f"[b yellow]\\[W][/] {''.join(message)}")

    def wait(self, *message: str) -> None:
        print(f"[b yellow]\\[B][/] {''.join(message)}")
        self.failed = True

    def blocked(self, *message: str) -> NoReturn:
        print(f"[b yellow]\\[B][/] {''.join(message)}")
        raise SystemExit(1)

    def fail(self, *message: str) -> None:
        print(f"[b red]\\[N][/] {''.join(message)}")
        self.failed = True

    def fatal(self, *message: str) -> NoReturn:
        print(f"[b red]\\[N][/] {''.join(message)}")
        raise SystemExit(1)

    def ensure_success(self) -> None:
        if self.failed:
            raise SystemExit(1)


def initialize_rich() -> None:
    reconfigure(highlight=False)


def get_github_instance() -> Github:
    try:
        token = run_stdout("gh", "auth", "token").strip()
        print("Using GitHub token from `gh auth token`")
        return Github(auth=Auth.Token(token))
    except Exception:
        Checklist().fatal("Failed to get GitHub token from `gh auth token`")


def get_releases_branch(version: Version) -> str:
    return f"releases/{version.base}"


def get_bump_branch(version: Version) -> str:
    return f"bump/{version.base}"


def get_backport_label(version: Version) -> str:
    return f"backport {get_releases_branch(version)}"


def get_blocking_label(version: Version) -> str:
    return f"blocks-release-{version.base}"


def get_latest_nightly_tag(grepo: Repository) -> Tag:
    for tag in grepo.get_tags():
        return tag
    raise SystemExit("No lean4 nightly tags found")


def get_file_contents(grepo: Repository, ref: str, path: str | Path) -> str:
    if isinstance(path, Path):
        assert not path.is_absolute()
        path = str(path)

    try:
        file = grepo.get_contents(path, ref=ref)
    except UnknownObjectException:
        raise SystemExit(f"Failed to read {path!r} from {ref!r} in {grepo.full_name!r}")
    if isinstance(file, list):
        raise SystemExit(f"Failed to read {path!r} from {ref!r} in {grepo.full_name!r}")
    return file.decoded_content.decode("utf-8")


def edit(
    path: Path, pattern: Pattern[str] | str, repl: Callable[[Match[str]], str] | str
) -> None:
    text = path.read_text()
    text = re.sub(pattern, repl, text)
    path.write_text(text)


#########
## PRs ##
#########


def fmt_pr(pr: PullRequest | Issue) -> str:
    return f"[link={pr.html_url}][green]#{pr.number}[/green] [b u]{e(pr.title)}[/b u][/link]"


def find_pr(grepo: Repository, head: str, base: str, title: str) -> PullRequest | None:
    head = f"{grepo.owner.login}:{head}"

    for pr in grepo.get_pulls(
        state="all", head=head, base=base, sort="created", direction="desc"
    ).get_page(0):
        return pr

    for pr in grepo.get_pulls(
        state="all", base=base, sort="created", direction="desc"
    ).get_page(0):
        if title in pr.title:
            return pr


def create_pr(grepo: Repository, head: str, base: str, title: str) -> PullRequest:
    head = f"{grepo.owner.login}:{head}"
    return grepo.create_pull(head=head, base=base, title=title)


# https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/proposing-changes-to-your-work-with-pull-requests/using-query-parameters-to-create-a-pull-request
def create_pr_url(
    base: ReleaseRepo,
    base_branch: str,
    head: ReleaseRepo,
    head_branch: str,
    title: str,
    body: str = "",
) -> str:
    url = f"{base.gh_url}/compare/{base_branch}...{head.gh_owner}:{head.gh_name}:{head_branch}"
    params = {"title": title, "body": body}
    return f"{url}?{urllib.parse.urlencode(params)}"


###################
## Cmake version ##
###################


@dataclass
class CMakeVersion:
    version: Version
    is_release: bool


def _parse_cmake_set(text: str, component: str) -> int:
    match = re.search(rf"set\({component}\s+(\d+) ", text)
    if not match:
        raise ValueError(f"Failed to parse {component} from CMakeLists.txt")
    return int(match.group(1))


def _update_cmake_set(text: str, component: str, value: int) -> str:
    return re.sub(rf"set\({component}\s+\d+ ", f"set({component} {value} ", text)


def get_cmake_version(grepo: Repository, ref: str) -> CMakeVersion:
    text = get_file_contents(grepo, ref, "src/CMakeLists.txt")
    major = _parse_cmake_set(text, "LEAN_VERSION_MAJOR")
    minor = _parse_cmake_set(text, "LEAN_VERSION_MINOR")
    patch = _parse_cmake_set(text, "LEAN_VERSION_PATCH")
    is_release = _parse_cmake_set(text, "LEAN_VERSION_IS_RELEASE")
    return CMakeVersion(Version(major, minor, patch), bool(is_release))


def set_cmake_version(lrepo: LocalRepo, version: CMakeVersion) -> None:
    cmakelists = lrepo.path / "src" / "CMakeLists.txt"
    text = cmakelists.read_text()
    text = _update_cmake_set(text, "LEAN_VERSION_MAJOR", version.version.major)
    text = _update_cmake_set(text, "LEAN_VERSION_MINOR", version.version.minor)
    text = _update_cmake_set(text, "LEAN_VERSION_PATCH", version.version.patch)
    text = _update_cmake_set(text, "LEAN_VERSION_IS_RELEASE", int(version.is_release))
    cmakelists.write_text(text)


###################
## Release notes ##
###################


def get_release_notes_path_for(version: Version) -> str:
    stem = str(version.stable).replace(".", "_")
    return f"Manual/Releases/{stem}.lean"


def get_release_notes_title_for(version: Version, release: GitRelease) -> str:
    date = release.created_at.astimezone(datetime.timezone.utc).strftime("%Y-%m-%d")
    return f"Lean {version.raw} ({date})"


def get_release_notes_title(grepo: Repository, version: Version) -> str | None:
    path = get_release_notes_path_for(version)
    try:
        text = get_file_contents(grepo, grepo.default_branch, path)
    except SystemExit:
        return None

    match = re.search(r'#doc \(Manual\) "(.+)" =>', text)
    if match is None:
        raise ValueError(f"Failed to parse release notes title from {grepo.full_name}")
    return match.group(1)


def set_release_notes_title(
    lrepo: LocalRepo, version: Version, release: GitRelease
) -> None:
    file = lrepo.path / get_release_notes_path_for(version)
    title = get_release_notes_title_for(version, release)
    edit(file, r'#doc \(Manual\) ".+" =>', f'#doc (Manual) "{title}" =>')


###############
## Toolchain ##
###############


def get_toolchain_for(version: Version) -> str:
    return f"leanprover/lean4:{version.tag}"


def get_toolchain(grepo: Repository, ref: str) -> str:
    return get_file_contents(grepo, ref, "lean-toolchain").strip()


def set_toolchain(path: Path, tag: str) -> None:
    toolchain_file = path / "lean-toolchain"
    toolchain_file.write_text(f"leanprover/lean4:{tag}\n")


#####################
## Toolchain bumps ##
#####################


def get_toolchain_bump_message(version: Version) -> str:
    return f"chore: bump toolchain to {version}"


# Assumes the PR has been merged into master in some way
# Assumes the commit message is predictable
def find_merged_toolchain_bump_sha(lrepo: LocalRepo, version: Version) -> str:
    n = 100
    expected = get_toolchain_bump_message(version)

    for line in lrepo.git_stdout(
        "log",
        "origin",
        "--pretty=format:%H %s",
        f"--max-count={n}",
    ).splitlines():
        sha, message = line.split(" ", 1)
        if message == expected or message.startswith(expected + " "):
            return sha

    raise SystemExit(f"Failed to find release commit in {n} latest commits")


###########################
## ProofWidgets releases ##
###########################


def get_proofwidgets_release_for(grepo: Repository, version: Version) -> Tag | None:
    expected_toolchain = get_toolchain_for(version)
    for tag in grepo.get_tags().get_page(0):
        if not re.fullmatch(r"v0\.0\.\d+", tag.name):
            continue
        toolchain = get_file_contents(grepo, tag.commit.sha, "lean-toolchain")
        if toolchain.strip() == expected_toolchain:
            return tag


def get_next_proofwidgets_release(grepo: Repository) -> str:
    for tag in grepo.get_tags():
        if match := re.fullmatch(r"v0\.0\.(\d+)", tag.name):
            patch = int(match.group(1))
            return f"v0.0.{patch + 1}"
    raise SystemExit("No releases found in tags")


##################################
## lean4-unicode-basic releases ##
##################################


def get_lean_unicode_basic_release_for(
    grepo: Repository, version: Version
) -> Tag | None:
    expected_toolchain = get_toolchain_for(version)
    for tag in grepo.get_tags().get_page(0):
        if not re.fullmatch(r"v\d+\.\d+\.\d+", tag.name):
            continue
        toolchain = get_file_contents(grepo, tag.commit.sha, "lean-toolchain")
        if toolchain.strip() == expected_toolchain:
            return tag
