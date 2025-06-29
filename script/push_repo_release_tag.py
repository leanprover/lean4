#!/usr/bin/env python3
import sys
import subprocess
import requests

def main():
    if len(sys.argv) != 4:
        print("Usage: ./push_repo_release_tag.py <repo> <branch> <version_tag>")
        sys.exit(1)

    repo, branch, version_tag = sys.argv[1], sys.argv[2], sys.argv[3]

    if branch not in {"master", "main"}:
        print(f"Error: Branch '{branch}' is not 'master' or 'main'.")
        sys.exit(1)

    # Get the `lean-toolchain` file content
    lean_toolchain_url = f"https://raw.githubusercontent.com/{repo}/{branch}/lean-toolchain"
    try:
        response = requests.get(lean_toolchain_url)
        response.raise_for_status()
    except requests.exceptions.RequestException as e:
        print(f"Error fetching 'lean-toolchain' file: {e}")
        sys.exit(1)

    lean_toolchain_content = response.text.strip()
    expected_prefix = "leanprover/lean4:"
    if not lean_toolchain_content.startswith(expected_prefix) or lean_toolchain_content != f"{expected_prefix}{version_tag}":
        print(f"Error: 'lean-toolchain' content does not match '{expected_prefix}{version_tag}'.")
        sys.exit(1)

    # Create and push the tag using `gh`
    try:
        # Check if the tag already exists
        list_tags_cmd = ["gh", "api", f"repos/{repo}/git/matching-refs/tags/v4", "--jq", ".[].ref"]
        list_tags_output = subprocess.run(list_tags_cmd, capture_output=True, text=True)

        if list_tags_output.returncode == 0:
            existing_tags = list_tags_output.stdout.strip().splitlines()
            if f"refs/tags/{version_tag}" in existing_tags:
                print(f"Error: Tag '{version_tag}' already exists.")
                print("Existing tags starting with 'v4':")
                for tag in existing_tags:
                    print(tag.replace("refs/tags/", ""))
                sys.exit(1)

        # Get the SHA of the branch
        get_sha_cmd = [
            "gh", "api", f"repos/{repo}/git/ref/heads/{branch}", "--jq", ".object.sha"
        ]
        sha_result = subprocess.run(get_sha_cmd, capture_output=True, text=True, check=True)
        sha = sha_result.stdout.strip()

        # Create the tag
        create_tag_cmd = [
            "gh", "api", f"repos/{repo}/git/refs",
            "-X", "POST",
            "-F", f"ref=refs/tags/{version_tag}",
            "-F", f"sha={sha}"
        ]
        subprocess.run(create_tag_cmd, capture_output=True, text=True, check=True)

        print(f"Successfully created and pushed tag '{version_tag}' to {repo}.")
    except subprocess.CalledProcessError as e:
        print(f"Error while creating/pushing tag: {e.stderr.strip() if e.stderr else e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
