#!/usr/bin/env python3
import sys
import subprocess
import requests

def check_gh_auth():
    """Check if GitHub CLI is properly authenticated."""
    try:
        result = subprocess.run(["gh", "auth", "status"], capture_output=True, text=True)
        if result.returncode != 0:
            return False, result.stderr
        return True, None
    except FileNotFoundError:
        return False, "GitHub CLI (gh) is not installed. Please install it first."
    except Exception as e:
        return False, f"Error checking authentication: {e}"

def handle_gh_error(error_output):
    """Handle GitHub CLI errors and provide helpful messages."""
    if "Not Found (HTTP 404)" in error_output:
        return "Repository not found or access denied. Please check:\n" \
               "1. The repository name is correct\n" \
               "2. You have access to the repository\n" \
               "3. Your GitHub CLI authentication is valid"
    elif "Bad credentials" in error_output or "invalid" in error_output.lower():
        return "Authentication failed. Please run 'gh auth login' to re-authenticate."
    elif "rate limit" in error_output.lower():
        return "GitHub API rate limit exceeded. Please try again later."
    else:
        return f"GitHub API error: {error_output}"

def main():
    if len(sys.argv) != 4:
        print("Usage: ./push_repo_release_tag.py <repo> <branch> <version_tag>")
        sys.exit(1)

    repo, branch, version_tag = sys.argv[1], sys.argv[2], sys.argv[3]

    if branch not in {"master", "main"}:
        print(f"Error: Branch '{branch}' is not 'master' or 'main'.")
        sys.exit(1)

    # Check GitHub CLI authentication first
    auth_ok, auth_error = check_gh_auth()
    if not auth_ok:
        print(f"Authentication error: {auth_error}")
        print("\nTo fix this, run: gh auth login")
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
        elif list_tags_output.returncode != 0:
            # Handle API errors when listing tags
            error_msg = handle_gh_error(list_tags_output.stderr)
            print(f"Error checking existing tags: {error_msg}")
            sys.exit(1)

        # Get the SHA of the branch
        get_sha_cmd = [
            "gh", "api", f"repos/{repo}/git/ref/heads/{branch}", "--jq", ".object.sha"
        ]
        sha_result = subprocess.run(get_sha_cmd, capture_output=True, text=True)
        
        if sha_result.returncode != 0:
            error_msg = handle_gh_error(sha_result.stderr)
            print(f"Error getting branch SHA: {error_msg}")
            sys.exit(1)
            
        sha = sha_result.stdout.strip()

        # Create the tag
        create_tag_cmd = [
            "gh", "api", f"repos/{repo}/git/refs",
            "-X", "POST",
            "-F", f"ref=refs/tags/{version_tag}",
            "-F", f"sha={sha}"
        ]
        create_result = subprocess.run(create_tag_cmd, capture_output=True, text=True)
        
        if create_result.returncode != 0:
            error_msg = handle_gh_error(create_result.stderr)
            print(f"Error creating tag: {error_msg}")
            sys.exit(1)

        print(f"Successfully created and pushed tag '{version_tag}' to {repo}.")
    except subprocess.CalledProcessError as e:
        error_msg = handle_gh_error(e.stderr.strip() if e.stderr else str(e))
        print(f"Error while creating/pushing tag: {error_msg}")
        sys.exit(1)
    except Exception as e:
        print(f"Unexpected error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
