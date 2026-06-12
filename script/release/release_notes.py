import datetime
import re
from argparse import ArgumentParser, Namespace
from dataclasses import dataclass
from pathlib import Path

import repos
from git import Commit, Repo
from github.Repository import Repository
from rich import print
from rich.markup import escape as e
from rich.prompt import IntPrompt

import util
from util import Version

SECTIONS = [
    "Language",
    "Library",
    "Tactics",
    "Compiler",
    "Pretty Printing",
    "Documentation",
    "Server",
    "Lake",
    "Other",
    "Uncategorised",
]


def link_commit(commit: Commit, title: str) -> str:
    link = f"{repos.LEAN4.gh_url}/commit/{commit.hexsha}"
    return f"[u link={link}]{e(title)}[/]"


def print_commit(commit: Commit, title: str) -> None:
    print(f"{link_commit(commit, title)}")


def get_commits_for(repo: Repo, version: Version) -> list[Commit]:
    print(f"Loading commits for range [cyan]{version.prev}[/]..[cyan]{version}[/]")
    return list(repo.iter_commits(f"{version.prev}..{version}"))


def get_commit_message(commit: Commit) -> tuple[str, str]:
    message = commit.message
    if isinstance(message, bytes):
        message = message.decode("utf-8")

    title, *body = message.splitlines()
    return title.strip(), "\n".join(body).strip()


def parse_pr_number(title: str) -> int | None:
    if match := re.search(r"\(\#(\d+)\)$", title):
        return int(match.group(1))


def parse_pr_title(title: str) -> tuple[str, str] | None:
    parts = title.split(":", 1)
    if len(parts) != 2:
        return None
    kind, content = parts
    return kind, content


def parse_backport_pr_body(body: str) -> int | None:
    match = re.search(r"Backport .* from #(\d+)", body)
    if not match:
        return
    return int(match.group(1))


def get_description_from_body(body: str) -> str:
    paragraphs = []
    paragraph = []
    in_code_block = False

    def flush() -> None:
        nonlocal paragraph
        if paragraph:
            paragraphs.append("\n".join(paragraph))
            paragraph = []

    for line in body.splitlines():
        if line.startswith("```"):
            in_code_block = not in_code_block
        if not in_code_block and line.strip() == "":
            flush()
            continue
        paragraph.append(line)
        if not in_code_block and line.strip() == "```":
            flush()
    flush()

    if not paragraphs:
        return ""

    description = paragraphs[0]
    if paragraphs[0].endswith(":"):
        description = "\n\n".join(paragraphs[:2])

    if description.startswith("This PR "):
        return description[len("This PR ") :]

    return ""  # Body has incorrect format


def get_category(labels: set[str]) -> str | None:
    cats = {
        label[len("changelog-") :] for label in labels if label.startswith("changelog-")
    }
    if len(cats) > 1:
        print(f"[red]Warning: Multiple changelog-* labels found: {cats}[/]")
    if not cats:
        return

    cat = cats.pop()
    if cat == "doc":
        return "Documentation"
    if cat == "pp":
        return "Pretty Printing"
    return cat.capitalize()


@dataclass
class CommitInfo:
    pr: int
    kind: str
    category: str | None
    description: str


def load_commits(version: Version, repo: Repo, grepo: Repository) -> list[CommitInfo]:
    skip_pr_number_prompt = False

    commits = []
    for commit in get_commits_for(repo, version):
        title, _ = get_commit_message(commit)
        print_commit(commit, title)

        if title == "chore: update stage0" or title.startswith("chore: CI: bump "):
            print("[blue]Ignored[/]")
            continue

        pr_number = parse_pr_number(title)
        if pr_number is None and skip_pr_number_prompt:
            print("[red]No PR number in title, skipping[/]")
            continue
        elif pr_number is None:
            pr_number = IntPrompt.ask("[red]No PR number in title.[/] PR", default=-1)
            if pr_number < 0:
                print("[red]Invalid PR number, skipping[/]")
                if pr_number == -2:
                    print("[red]Skipping PR number prompt for remaining commits[/]")
                    skip_pr_number_prompt = True
                continue

        pr = grepo.get_pull(pr_number)
        if backported := parse_backport_pr_body(pr.body or ""):
            print(f"[yellow]PR is a backport of #{backported}[/]")
            pr_number = backported
            pr = grepo.get_pull(pr_number)

        parsed = parse_pr_title(pr.title)
        if parsed is None:
            print("[red]Title does not match expected format[/]")
            continue

        # Intentionally overwriting commit title with PR title
        kind, title = parsed
        warn = kind in {"feat", "fix"}

        labels = {label.name for label in pr.get_labels()}
        if "changelog-no" in labels:
            print("[blue]Ignored, labeled [b]changelog-no[/b][/]")
            continue

        description = get_description_from_body(pr.body or "")
        if not description:
            if warn:
                print("[yellow]No description in body[/]")
            description = title

        category = get_category(labels)
        if not category:
            if warn:
                print("[yellow]No changelog-* label found[/]")
        if category is not None and category not in SECTIONS:
            print(f"[yellow]Unknown category {category!r}[/]")
            category = "Uncategorised"

        info = CommitInfo(
            pr=pr_number,
            kind=kind,
            category=category,
            description=description,
        )
        commits.append(info)

    return commits


@dataclass
class CommitCounts:
    total: int
    feat: int
    fix: int
    refactor: int
    doc: int
    perf: int
    test: int
    other: int


def count_by_kind(commits: list[CommitInfo]) -> CommitCounts:
    feat = 0
    fix = 0
    refactor = 0
    doc = 0
    perf = 0
    test = 0
    other = 0
    for commit in commits:
        if commit.kind == "feat":
            feat += 1
        elif commit.kind == "fix":
            fix += 1
        elif commit.kind == "refactor":
            refactor += 1
        elif commit.kind == "doc":
            doc += 1
        elif commit.kind == "perf":
            perf += 1
        elif commit.kind == "test":
            test += 1
        else:
            other += 1
    return CommitCounts(
        total=len(commits),
        feat=feat,
        fix=fix,
        refactor=refactor,
        doc=doc,
        perf=perf,
        test=test,
        other=other,
    )


def pl(n: int, singular: str, plural: str | None = None) -> str:
    plural = singular + "s" if plural is None else plural
    return f"{n} {singular if n == 1 else plural}"


def main(version: Version, refman: Path):
    util.initialize_rich()
    github = util.get_github_instance()

    repo = Repo(Path(__file__).parent.parent.parent)
    grepo = github.get_repo(repos.LEAN4.gh_full_name)
    release = grepo.get_release(version.tag)
    date = release.created_at.astimezone(datetime.timezone.utc)
    title = util.get_release_notes_title_for(version, release)

    commits = load_commits(version, repo, grepo)
    counts = count_by_kind(commits)

    lines = []
    lines.append("/-")
    lines.append(f"Copyright (c) {date.year} Lean FRO LLC. All rights reserved.")
    lines.append("Released under Apache 2.0 license as described in the file LICENSE.")
    lines.append("Author: Joscha Mennicken")
    lines.append("-/")
    lines.append("")
    lines.append("import VersoManual")
    lines.append("import Manual.Meta")
    lines.append("import Manual.Meta.Markdown")
    lines.append("")
    lines.append("open Manual")
    lines.append("open Verso.Genre")
    lines.append("open Verso.Genre.Manual")
    lines.append("open Verso.Genre.Manual.InlineLean")
    lines.append("")
    lines.append(f'#doc (Manual) "{title}" =>')
    lines.append("%%%")
    lines.append(f'tag := "release-{version.stable}"')
    lines.append(f'file := "{version.stable}"')
    lines.append("%%%")
    if not version.is_stable:
        lines.append("")
        lines.append(":::warn")
        lines.append(
            "These release notes describe a _release candidate_, not the final release."
        )
        lines.append("They may be incomplete and are subject to change.")
        lines.append(":::")
    lines.append("")
    lines.append(f"For this release, {pl(counts.total, 'change')} landed.")
    lines.append(f"In addition to the {pl(counts.feat, 'feature addition')},")
    lines.append(f"and {pl(counts.fix, 'fix', 'fixes')} listed below,")
    lines.append(f"there were {pl(counts.refactor, 'refactoring change')},")
    lines.append(f"{pl(counts.doc, 'documentation improvement')},")
    lines.append(f"{pl(counts.perf, 'performance improvement')},")
    lines.append(f"{pl(counts.test, 'improvement')} to the test suite,")
    lines.append(f"and {pl(counts.other, 'other change')}.")
    for section in SECTIONS:
        for_section = [commit for commit in commits if commit.category == section]
        if not for_section:
            continue
        lines.append("")
        lines.append(f"# {section}")
        lines.append("")
        lines.append("````markdown")
        for commit in for_section:
            lines.append("")
            lines.append(f"- [#{commit.pr}]({repos.LEAN4.gh_url}/pull/{commit.pr})")
            for line in commit.description.splitlines():
                lines.append(f"  {line}".rstrip())
        lines.append("")
        lines.append("````")

    out = refman / util.get_release_notes_path_for(version)
    out.write_text("\n".join(lines) + "\n")


class Args(Namespace):
    version: Version
    refman: Path


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("version", type=Version.parse)
    parser.add_argument("refman", type=Path)
    args = parser.parse_args(namespace=Args)
    main(args.version, args.refman)
