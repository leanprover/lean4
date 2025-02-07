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

def strip_rc_suffix(toolchain):
    """Remove -rcX suffix from the toolchain."""
    return toolchain.split("-")[0]

def branch_exists(repo_url, branch, github_token):
    api_url = repo_url.replace("https://github.com/", "https://api.github.com/repos/") + f"/branches/{branch}"
    headers = {'Authorization': f'token {github_token}'} if github_token else {}
    response = requests.get(api_url, headers=headers)
    return response.status_code == 200

def tag_exists(repo_url, tag_name, github_token):
    # Use /git/matching-refs/tags/ to get all matching tags
    api_url = repo_url.replace("https://github.com/", "https://api.github.com/repos/") + f"/git/matching-refs/tags/{tag_name}"
    headers = {'Authorization': f'token {github_token}'} if github_token else {}
    response = requests.get(api_url, headers=headers)

    if response.status_code != 200:
        return False

    # Check if any of the returned refs exactly match our tag
    matching_tags = response.json()
    return any(tag["ref"] == f"refs/tags/{tag_name}" for tag in matching_tags)

def release_page_exists(repo_url, tag_name, github_token):
    api_url = repo_url.replace("https://github.com/", "https://api.github.com/repos/") + f"/releases/tags/{tag_name}"
    headers = {'Authorization': f'token {github_token}'} if github_token else {}
    response = requests.get(api_url, headers=headers)
    return response.status_code == 200

def get_release_notes(repo_url, tag_name, github_token):
    api_url = repo_url.replace("https://github.com/", "https://api.github.com/repos/") + f"/releases/tags/{tag_name}"
    headers = {'Authorization': f'token {github_token}'} if github_token else {}
    response = requests.get(api_url, headers=headers)
    if response.status_code == 200:
        return response.json().get("body", "").strip()
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

def parse_version(version_str):
    # Remove 'v' prefix and extract version and release candidate suffix
    if ':' in version_str:
        version_str = version_str.split(':')[1]
    version = version_str.lstrip('v')
    parts = version.split('-')
    base_version = tuple(map(int, parts[0].split('.')))
    rc_part = parts[1] if len(parts) > 1 and parts[1].startswith('rc') else None
    rc_number = int(rc_part[2:]) if rc_part else float('inf')  # Treat non-rc as higher than rc
    return base_version + (rc_number,)

def is_version_gte(version1, version2):
    """Check if version1 >= version2, including proper handling of release candidates."""
    return parse_version(version1) >= parse_version(version2)

def is_merged_into_stable(repo_url, tag_name, stable_branch, github_token):
    # First get the commit SHA for the tag
    api_base = repo_url.replace("https://github.com/", "https://api.github.com/repos/")
    headers = {'Authorization': f'token {github_token}'} if github_token else {}

    # Get tag's commit SHA
    tag_response = requests.get(f"{api_base}/git/refs/tags/{tag_name}", headers=headers)
    if tag_response.status_code != 200:
        return False
    
    # Handle both single object and array responses
    tag_data = tag_response.json()
    if isinstance(tag_data, list):
        # Find the exact matching tag in the list
        matching_tags = [tag for tag in tag_data if tag['ref'] == f'refs/tags/{tag_name}']
        if not matching_tags:
            return False
        tag_sha = matching_tags[0]['object']['sha']
    else:
        tag_sha = tag_data['object']['sha']

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

def is_release_candidate(version):
    return "-rc" in version

def check_cmake_version(repo_url, branch, version_major, version_minor, github_token):
    """Verify the CMake version settings in src/CMakeLists.txt."""
    cmake_file_path = "src/CMakeLists.txt"
    content = get_branch_content(repo_url, branch, cmake_file_path, github_token)
    if content is None:
        print(f"  ❌ Could not retrieve {cmake_file_path} from {branch}")
        return False

    expected_lines = [
        f"set(LEAN_VERSION_MAJOR {version_major})",
        f"set(LEAN_VERSION_MINOR {version_minor})",
        f"set(LEAN_VERSION_PATCH 0)",
        f"set(LEAN_VERSION_IS_RELEASE 1)"
    ]

    for line in expected_lines:
        if not any(l.strip().startswith(line) for l in content.splitlines()):
            print(f"  ❌ Missing or incorrect line in {cmake_file_path}: {line}")
            return False

    print(f"  ✅ CMake version settings are correct in {cmake_file_path}")
    return True

def extract_org_repo_from_url(repo_url):
    """Extract the 'org/repo' part from a GitHub URL."""
    if repo_url.startswith("https://github.com/"):
        return repo_url.replace("https://github.com/", "").rstrip("/")
    return repo_url

def get_next_version(version):
    """Calculate the next version number, ignoring RC suffix."""
    # Strip v prefix and RC suffix if present
    base_version = strip_rc_suffix(version.lstrip('v'))
    major, minor, patch = map(int, base_version.split('.'))
    # Next version is always .0
    return f"v{major}.{minor + 1}.0"

def check_bump_branch_toolchain(url, bump_branch, github_token):
    """Check if the lean-toolchain file in bump branch starts with either 'leanprover/lean4:nightly-' or the next version."""
    content = get_branch_content(url, bump_branch, "lean-toolchain", github_token)
    if content is None:
        print(f"  ❌ No lean-toolchain file found in {bump_branch} branch")
        return False
    
    # Extract the next version from the bump branch name (bump/v4.X.0)
    next_version = bump_branch.split('/')[1]
    
    if not (content.startswith("leanprover/lean4:nightly-") or 
            content.startswith(f"leanprover/lean4:{next_version}")):
        print(f"  ❌ Bump branch toolchain should use either nightly or {next_version}, but found: {content}")
        return False
    
    print(f"  ✅ Bump branch correctly uses toolchain: {content}")
    return True

def main():
    github_token = get_github_token()

    if len(sys.argv) != 2:
        print("Usage: python3 release_checklist.py <toolchain>")
        sys.exit(1)

    toolchain = sys.argv[1]
    stripped_toolchain = strip_rc_suffix(toolchain)
    lean_repo_url = "https://github.com/leanprover/lean4"

    # Preliminary checks
    print("\nPerforming preliminary checks...")

    # Check for branch releases/v4.Y.0
    version_major, version_minor, _ = map(int, stripped_toolchain.lstrip('v').split('.'))
    branch_name = f"releases/v{version_major}.{version_minor}.0"
    if branch_exists(lean_repo_url, branch_name, github_token):
        print(f"  ✅ Branch {branch_name} exists")

        # Check CMake version settings
        check_cmake_version(lean_repo_url, branch_name, version_major, version_minor, github_token)
    else:
        print(f"  ❌ Branch {branch_name} does not exist")

    # Check for tag v4.X.Y(-rcZ)
    if tag_exists(lean_repo_url, toolchain, github_token):
        print(f"  ✅ Tag {toolchain} exists")
    else:
        print(f"  ❌ Tag {toolchain} does not exist.")

    # Check for release page
    if release_page_exists(lean_repo_url, toolchain, github_token):
        print(f"  ✅ Release page for {toolchain} exists")

        # Check the first line of the release notes
        release_notes = get_release_notes(lean_repo_url, toolchain, github_token)
        if release_notes and toolchain in release_notes.splitlines()[0].strip():
            print(f"  ✅ Release notes look good.")
        else:
            previous_minor_version = version_minor - 1
            previous_release = f"v{version_major}.{previous_minor_version}.0"
            print(f"  ❌ Release notes not published. Please run `script/release_notes.py --since {previous_release}` on branch `{branch_name}`.")
    else:
        print(f"  ❌ Release page for {toolchain} does not exist")

    # Load repositories and perform further checks
    print("\nChecking repositories...")

    with open(os.path.join(os.path.dirname(__file__), "release_repos.yml")) as f:
        repos = yaml.safe_load(f)["repositories"]

    for repo in repos:
        name = repo["name"]
        url = repo["url"]
        branch = repo["branch"]
        check_stable = repo["stable-branch"]
        check_tag = repo.get("toolchain-tag", True)
        check_bump = repo.get("bump-branch", False)

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
                print(f"  ❌ Tag {toolchain} does not exist. Run `script/push_repo_release_tag.py {extract_org_repo_from_url(url)} {branch} {toolchain}`.")
            else:
                print(f"  ✅ Tag {toolchain} exists")

        # Only check merging into stable if stable-branch is true and not a release candidate
        if check_stable and not is_release_candidate(toolchain):
            if not is_merged_into_stable(url, toolchain, "stable", github_token):
                print(f"  ❌ Tag {toolchain} is not merged into stable")
            else:
                print(f"  ✅ Tag {toolchain} is merged into stable")

        # Check for bump branch if configured
        if check_bump:
            next_version = get_next_version(toolchain)
            bump_branch = f"bump/{next_version}"
            if branch_exists(url, bump_branch, github_token):
                print(f"  ✅ Bump branch {bump_branch} exists")
                check_bump_branch_toolchain(url, bump_branch, github_token)
            else:
                print(f"  ❌ Bump branch {bump_branch} does not exist")

    # Check lean4 master branch for next development cycle
    print("\nChecking lean4 master branch configuration...")
    next_version = get_next_version(toolchain)
    next_minor = int(next_version.split('.')[1])
    
    cmake_content = get_branch_content(lean_repo_url, "master", "src/CMakeLists.txt", github_token)
    if cmake_content is None:
        print("  ❌ Could not retrieve CMakeLists.txt from master")
    else:
        cmake_lines = cmake_content.splitlines()
        # Find the actual minor version in CMakeLists.txt
        for line in cmake_lines:
            if line.strip().startswith("set(LEAN_VERSION_MINOR "):
                actual_minor = int(line.split()[-1].rstrip(")"))
                version_minor_correct = actual_minor >= next_minor
                break
        else:
            version_minor_correct = False
            
        is_release_correct = any(
            l.strip().startswith("set(LEAN_VERSION_IS_RELEASE 0)") 
            for l in cmake_lines
        )
        
        if not (version_minor_correct and is_release_correct):
            print("  ❌ lean4 needs a \"begin dev cycle\" PR")
        else:
            print("  ✅ lean4 master branch is configured for next development cycle")

if __name__ == "__main__":
    main()
