#!/usr/bin/env python3

import argparse
import yaml
import requests
import base64
import subprocess
import sys
import os

def parse_repos_config(file_path):
    with open(file_path, "r") as f:
        return yaml.safe_load(f)["repositories"]

def get_github_token():
    try:
        import subprocess
        result = subprocess.run(['gh', 'auth', 'token'], capture_output=True, text=True)
        if result.returncode == 0:
            return result.stdout.strip()
    except FileNotFoundError:
        print("Warning: 'gh' CLI not found. Some API calls may be rate-limited.")
    return None

def get_branch_content(repo_url, branch, file_path, github_token):
    api_url = repo_url.replace("https://github.com/", "https://api.github.com/repos/") + f"/contents/{file_path}?ref={branch}"
    headers = {'Authorization': f'token {github_token}'} if github_token else {}
    response = requests.get(api_url, headers=headers)
    if response.status_code == 200:
        content = response.json().get("content", "")
        content = content.replace("\n", "")
        try:
            return base64.b64decode(content).decode('utf-8').strip()
        except Exception:
            return None
    return None

def tag_exists(repo_url, tag_name, github_token):
    api_url = repo_url.replace("https://github.com/", "https://api.github.com/repos/") + f"/git/refs/tags/{tag_name}"
    headers = {'Authorization': f'token {github_token}'} if github_token else {}
    response = requests.get(api_url, headers=headers)
    return response.status_code == 200

def is_merged_into_stable(repo_url, tag_name, stable_branch, github_token):
    # First get the commit SHA for the tag
    api_base = repo_url.replace("https://github.com/", "https://api.github.com/repos/")
    headers = {'Authorization': f'token {github_token}'} if github_token else {}

    # Get tag's commit SHA
    tag_response = requests.get(f"{api_base}/git/refs/tags/{tag_name}", headers=headers)
    if tag_response.status_code != 200:
        return False
    tag_sha = tag_response.json()['object']['sha']

    # Get commits on stable branch containing this SHA
    commits_response = requests.get(
        f"{api_base}/commits?sha={stable_branch}&per_page=100",
        headers=headers
    )
    if commits_response.status_code != 200:
        return False

    # Check if any commit in stable's history matches our tag's SHA
    stable_commits = [commit['sha'] for commit in commits_response.json()]
    return tag_sha in stable_commits

def parse_version(version_str):
    # Remove 'v' prefix and split into components
    # Handle Lean toolchain format (leanprover/lean4:v4.x.y)
    if ':' in version_str:
        version_str = version_str.split(':')[1]
    version = version_str.lstrip('v')
    # Handle release candidates by removing -rc part for comparison
    version = version.split('-')[0]
    return tuple(map(int, version.split('.')))

def is_version_gte(version1, version2):
    """Check if version1 >= version2"""
    return parse_version(version1) >= parse_version(version2)

def is_release_candidate(version):
    return "-rc" in version

def main():
    github_token = get_github_token()

    if len(sys.argv) != 2:
        print("Usage: python3 release_checklist.py <toolchain>")
        sys.exit(1)

    toolchain = sys.argv[1]

    with open(os.path.join(os.path.dirname(__file__), "release_repos.yml")) as f:
        repos = yaml.safe_load(f)["repositories"]

    for repo in repos:
        name = repo["name"]
        url = repo["url"]
        branch = repo["branch"]
        check_stable = repo["stable-branch"]
        check_tag = repo.get("toolchain-tag", True)

        print(f"\nRepository: {name}")

        # Check if branch is on at least the target toolchain
        lean_toolchain_content = get_branch_content(url, branch, "lean-toolchain", github_token)
        if lean_toolchain_content is None:
            print(f"  ❌ No lean-toolchain file found in {branch} branch")
            continue

        on_target_toolchain = is_version_gte(lean_toolchain_content.strip(), toolchain)
        if not on_target_toolchain:
            print(f"  ❌ Not on target toolchain (needs ≥ {toolchain}, but {branch} is on {lean_toolchain_content.strip()})")
            continue
        print(f"  ✅ On compatible toolchain (>= {toolchain})")

        # Only check for tag if toolchain-tag is true
        if check_tag:
            if not tag_exists(url, toolchain, github_token):
                print(f"  ❌ Tag {toolchain} does not exist")
                continue
            print(f"  ✅ Tag {toolchain} exists")

        # Only check merging into stable if stable-branch is true and not a release candidate
        if check_stable and not is_release_candidate(toolchain):
            if not is_merged_into_stable(url, toolchain, "stable", github_token):
                print(f"  ❌ Tag {toolchain} is not merged into stable")
                continue
            print(f"  ✅ Tag {toolchain} is merged into stable")

if __name__ == "__main__":
    main()
