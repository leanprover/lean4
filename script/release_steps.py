#!/usr/bin/env python3

"""
Generate release steps script for Lean4 repositories.

This script helps automate the release process for Lean4 and its dependent repositories
by generating step-by-step instructions for updating toolchains, creating tags,
and managing branches.

Usage:
    python3 release_steps.py <version> <repo>

Arguments:
    version: The version to set in the lean-toolchain file (e.g., v4.6.0)
    repo: A substring of the repository name as specified in release_repos.yml

Example:
    python3 release_steps.py v4.6.0 mathlib
    python3 release_steps.py v4.6.0 batt

The script reads repository configurations from release_repos.yml in the same directory.
Each repository may have specific requirements for:
- Branch management
- Toolchain updates
- Dependency updates
- Tagging conventions
- Stable branch handling
"""

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
    repo_url = repo_config['url']
    # Extract the last component of the URL, removing the .git extension if present
    repo_dir = repo_url.split('/')[-1].replace('.git', '')
    default_branch = repo_config.get("branch", "main")
    dependencies = repo_config.get("dependencies", [])
    requires_tagging = repo_config.get("toolchain-tag", True)
    has_stable_branch = repo_config.get("stable-branch", True)

    script_lines = [
        f"cd {repo_dir}",
        "git fetch",
        f"git checkout {default_branch} && git pull",
        f"git checkout -b bump_to_{version}",
        f"echo leanprover/lean4:{version} > lean-toolchain",
    ]

    # Special cases for specific repositories
    if repo_name == "REPL":
        script_lines.extend([
            "lake update",
            "cd test/Mathlib",
            f"perl -pi -e 's/rev = \"v\\d+\\.\\d+\\.\\d+(-rc\\d+)?\"/rev = \"{version}\"/g' lakefile.toml",
            f"echo leanprover/lean4:{version} > lean-toolchain",
            "lake update",
            "cd ../..",
            "./test.sh"
        ])
    elif dependencies:
        script_lines.append('echo "Please update the dependencies in lakefile.{lean,toml}"')
        script_lines.append("lake update")

    script_lines.append("")

    script_lines.extend([
        f'git commit -am "chore: bump toolchain to {version}"',
        ""
    ])

    if re.search(r'rc\d+$', version) and repo_name in ["Batteries", "Mathlib"]:
        script_lines.extend([
            "echo 'This repo has nightly-testing infrastructure'",
            f"git merge origin/bump/{version.split('-rc')[0]}",
            "echo 'Please resolve any conflicts.'",
            ""
        ])
    if repo_name != "Mathlib":
        script_lines.extend([
            "lake build && if lake check-test; then lake test; fi",
            ""
        ])

    script_lines.extend([
        'gh pr create --title "chore: bump toolchain to ' + version + '" --body ""',
        "echo 'Please review the PR and merge it.'",
        ""
    ])

    return "\n".join(script_lines)

def main():
    parser = argparse.ArgumentParser(
        description="Generate release steps script for Lean4 repositories.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s v4.6.0 mathlib    Generate steps for updating Mathlib to v4.6.0
  %(prog)s v4.6.0 batt       Generate steps for updating Batteries to v4.6.0
  
The script will generate shell commands to:
1. Update the lean-toolchain file
2. Create appropriate branches and commits
3. Create pull requests

(Note that the steps of creating toolchain version tags, and merging these into `stable` branches,
are handled by `script/release_checklist.py`.)
"""
    )
    parser.add_argument("version", help="The version to set in the lean-toolchain file (e.g., v4.6.0)")
    parser.add_argument("repo", help="A substring of the repository name as specified in release_repos.yml")
    args = parser.parse_args()

    config_path = os.path.join(os.path.dirname(__file__), "release_repos.yml")
    config = load_repos_config(config_path)

    script = generate_script(args.repo, args.version, config)
    print(script)

if __name__ == "__main__":
    main()
