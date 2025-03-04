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
    default_branch = repo_config.get("branch", "main")
    dependencies = repo_config.get("dependencies", [])

    script_lines = [
        f"cd {repo_config['name']}",
        "git fetch",
        f"git checkout {default_branch}",
        f"echo leanprover/lean4:{version} > lean-toolchain",
    ]

    if dependencies:
        script_lines.append('echo "Please update the dependencies in lakefile.{lean,toml}"')

    script_lines.extend([
        "lake update",
        f'git commit -am "chore: bump toolchain to {version}"',
        "gh pr create"
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
