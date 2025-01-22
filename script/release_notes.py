#!/usr/bin/env python3

import sys
import re
import json
import requests
import subprocess
from collections import defaultdict
from git import Repo

def get_commits_since_tag(repo, tag):
    try:
        tag_commit = repo.commit(tag)
        commits = list(repo.iter_commits(f"{tag_commit.hexsha}..HEAD"))
        return [
            (commit.hexsha, commit.message.splitlines()[0], commit.message)
            for commit in commits
        ]
    except Exception as e:
        sys.stderr.write(f"Error retrieving commits: {e}\n")
        sys.exit(1)

def check_pr_number(first_line):
    match = re.search(r"\(\#(\d+)\)$", first_line)
    if match:
        return int(match.group(1))
    return None

def fetch_pr_labels(pr_number):
    try:
        # Use gh CLI to fetch PR details
        result = subprocess.run([
            "gh", "api", f"repos/leanprover/lean4/pulls/{pr_number}"
        ], capture_output=True, text=True, check=True)
        pr_data = result.stdout
        pr_json = json.loads(pr_data)
        return [label["name"] for label in pr_json.get("labels", [])]
    except subprocess.CalledProcessError as e:
        sys.stderr.write(f"Failed to fetch PR #{pr_number} using gh: {e.stderr}\n")
        return []

def format_section_title(label):
    title = label.replace("changelog-", "").capitalize()
    if title == "Doc":
        return "Documentation"
    elif title == "Pp":
        return "Pretty Printing"
    return title

def sort_sections_order():
    return [
        "Language",
        "Library",
        "Compiler",
        "Pretty Printing",
        "Documentation",
        "Server",
        "Lake",
        "Other",
        "Uncategorised"
    ]

def format_markdown_description(pr_number, description):
    link = f"[#{pr_number}](https://github.com/leanprover/lean4/pull/{pr_number})"
    return f"{link} {description}"

def main():
    if len(sys.argv) != 2:
        sys.stderr.write("Usage: script.py <git-tag>\n")
        sys.exit(1)

    tag = sys.argv[1]
    try:
        repo = Repo(".")
    except Exception as e:
        sys.stderr.write(f"Error opening Git repository: {e}\n")
        sys.exit(1)

    commits = get_commits_since_tag(repo, tag)

    sys.stderr.write(f"Found {len(commits)} commits since tag {tag}:\n")
    for commit_hash, first_line, _ in commits:
        sys.stderr.write(f"- {commit_hash}: {first_line}\n")

    changelog = defaultdict(list)

    for commit_hash, first_line, full_message in commits:
        # Skip commits with the specific first lines
        if first_line == "chore: update stage0" or first_line.startswith("chore: CI: bump "):
            continue

        pr_number = check_pr_number(first_line)

        if not pr_number:
            sys.stderr.write(f"No PR number found in {first_line}\n")
            continue

        # Remove the first line from the full_message for further processing
        body = full_message[len(first_line):].strip()

        paragraphs = body.split('\n\n')
        second_paragraph = paragraphs[0] if len(paragraphs) > 0 else ""

        labels = fetch_pr_labels(pr_number)

        # Skip entries with the "changelog-no" label
        if "changelog-no" in labels:
            continue

        report_errors = first_line.startswith("feat:") or first_line.startswith("fix:")

        if not second_paragraph.startswith("This PR "):
            if report_errors:
                sys.stderr.write(f"No PR description found in commit:\n{commit_hash}\n{first_line}\n{body}\n\n")
                fallback_description = re.sub(r":$", "", first_line.split(" ", 1)[1]).rsplit(" (#", 1)[0]
                markdown_description = format_markdown_description(pr_number, fallback_description)
            else:
                continue
        else:
            markdown_description = format_markdown_description(pr_number, second_paragraph.replace("This PR ", ""))

        changelog_labels = [label for label in labels if label.startswith("changelog-")]
        if len(changelog_labels) > 1:
            sys.stderr.write(f"Warning: Multiple changelog-* labels found for PR #{pr_number}: {changelog_labels}\n")

        if not changelog_labels:
            if report_errors:
                sys.stderr.write(f"Warning: No changelog-* label found for PR #{pr_number}\n")
            else:
                continue

        for label in changelog_labels:
            changelog[label].append((pr_number, markdown_description))

    section_order = sort_sections_order()
    sorted_changelog = sorted(changelog.items(), key=lambda item: section_order.index(format_section_title(item[0])) if format_section_title(item[0]) in section_order else len(section_order))

    for label, entries in sorted_changelog:
        section_title = format_section_title(label) if label != "Uncategorised" else "Uncategorised"
        print(f"## {section_title}\n")
        for _, entry in sorted(entries, key=lambda x: x[0]):
            print(f"* {entry}\n")

if __name__ == "__main__":
    main()
