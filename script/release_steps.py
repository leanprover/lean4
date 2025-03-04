#!/usr/bin/env python3

import argparse
import yaml
import os
import sys
import re

def load_repos_config(file_path):
    with open(file_path, "r") as f:
        return yaml.safe_load(f)["repositories"]

def find_repo(repo_substring, config):
    pattern = re.compile(re.escape(repo_substring), re.IGNORECASE)
    matching_repos = [r for r in config if pattern.search(r["name"])]
    if not matching_repos:
        print(f"Error: No repository matching '{repo_substring}' found in configuration.")
        sys.exit(1)
    if len(matching_repos) > 1:
        print(f"Error: Multiple repositories matching '{repo_substring}' found in configuration: {', '.join(r['name'] for r in matching_repos)}")
        sys.exit(1)
    return matching_repos[0]

def generate_script(repo, version, config):
    repo_config = find_repo(repo, config)
    repo_name = repo_config['name']
    default_branch = repo_config.get("branch", "main")
    dependencies = repo_config.get("dependencies", [])
    requires_tagging = repo_config.get("toolchain-tag", True)
    has_stable_branch = repo_config.get("stable-branch", True)

    script_lines = [
        f"cd {repo_name}",
        "git fetch",
        f"git checkout {default_branch}",
        f"git checkout -b bump_to_{version}",
        f"echo leanprover/lean4:{version} > lean-toolchain",
    ]

    # Special cases for specific repositories
    if repo_name == "REPL":
        script_lines.extend([
            "cd test/Mathlib",
            f"echo leanprover/lean4:{version} > lean-toolchain",
            'echo "Please update the dependencies in lakefile.{lean,toml}"',
            "lake update",
            "cd ../.."
        ])
    elif dependencies:
        script_lines.append('echo "Please update the dependencies in lakefile.{lean,toml}"')

    script_lines.append("lake update")
    script_lines.append("")

    if not re.search(r'rc\d+$', version) and repo_name in ["Batteries", "Mathlib"]:
        script_lines.extend([
            "echo 'This repo has nightly-testing infrastructure'",
            f"git merge bump/{version}",
            "echo 'Please resolve any conflicts.'",
            ""
        ])

    script_lines.extend([
        f'git commit -am "chore: bump toolchain to {version}"',
        "gh pr create",
        "echo 'Please review the PR and merge it.'",
        ""
    ])

    # Special cases for specific repositories
    if repo_name == "ProofWidgets4":
        script_lines.append(f"echo 'Note: Follow the version convention of the repository for tagging.'")
    elif requires_tagging:
        script_lines.append(f"git tag -a {version} -m 'Release {version}'")
        script_lines.append("git push origin --tags")

    if has_stable_branch:
        script_lines.extend([
            "git checkout stable",
            f"git merge {version}",
            "git push origin stable"
        ])

    return "\n".join(script_lines)

def main():
    parser = argparse.ArgumentParser(description="Generate release steps script.")
    parser.add_argument("version", help="The version to set in the lean-toolchain file.")
    parser.add_argument("repo", help="A substring of the repository name as specified in the YAML config.")
    args = parser.parse_args()

    config_path = os.path.join(os.path.dirname(__file__), "release_repos.yml")
    config = load_repos_config(config_path)

    script = generate_script(args.repo, args.version, config)
    print(script)

if __name__ == "__main__":
    main()
