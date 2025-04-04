#!/usr/bin/env python3

"""
Merge a tag into a branch on a GitHub repository.

This script checks if a specified tag can be merged cleanly into a branch and performs
the merge if possible. If the merge cannot be done cleanly, it prints a helpful message.

Usage:
    python3 merge_remote.py <org/repo> <branch> <tag>

Arguments:
    org/repo: GitHub repository in the format 'organization/repository'
    branch: The target branch to merge into
    tag: The tag to merge from

Example:
    python3 merge_remote.py leanprover/mathlib4 stable v4.6.0

The script uses the GitHub CLI (`gh`), so make sure it's installed and authenticated.
"""

import argparse
import subprocess
import sys
import tempfile
import os
import shutil


def run_command(command, check=True, capture_output=True):
    """Run a shell command and return the result."""
    try:
        result = subprocess.run(
            command,
            check=check,
            shell=True,
            text=True,
            capture_output=capture_output
        )
        return result
    except subprocess.CalledProcessError as e:
        if capture_output:
            print(f"Command failed: {command}")
            print(f"Error: {e.stderr}")
        return e


def clone_repo(repo, temp_dir):
    """Clone the repository to a temporary directory using shallow clone."""
    print(f"Shallow cloning {repo}...")
    # Keep the shallow clone for efficiency
    clone_result = run_command(f"gh repo clone {repo} {temp_dir} -- --depth=1", check=False)
    if clone_result.returncode != 0:
        print(f"Failed to clone repository {repo}.")
        print(f"Error: {clone_result.stderr}")
        return False
    return True


def check_and_merge(repo, branch, tag, temp_dir):
    """Check if tag can be merged into branch and perform the merge if possible."""
    # Change to the temporary directory
    os.chdir(temp_dir)
    
    # First fetch the specific remote branch with its history
    print(f"Fetching branch '{branch}'...")
    fetch_branch = run_command(f"git fetch origin {branch}:refs/remotes/origin/{branch} --update-head-ok")
    if fetch_branch.returncode != 0:
        print(f"Error: Failed to fetch branch '{branch}'.")
        return False
    
    # Then fetch the specific tag
    print(f"Fetching tag '{tag}'...")
    fetch_tag = run_command(f"git fetch origin tag {tag}")
    if fetch_tag.returncode != 0:
        print(f"Error: Failed to fetch tag '{tag}'.")
        return False
    
    # Check if branch exists now that we've fetched it
    branch_check = run_command(f"git branch -r | grep origin/{branch}")
    if branch_check.returncode != 0:
        print(f"Error: Branch '{branch}' does not exist in repository.")
        return False

    # Check if tag exists
    tag_check = run_command(f"git tag -l {tag}")
    if tag_check.returncode != 0 or not tag_check.stdout.strip():
        print(f"Error: Tag '{tag}' does not exist in repository.")
        return False

    # Checkout the branch
    print(f"Checking out branch '{branch}'...")
    checkout_result = run_command(f"git checkout -b {branch} origin/{branch}")
    if checkout_result.returncode != 0:
        return False

    # Try merging the tag in a dry-run to check if it can be merged cleanly
    print(f"Checking if {tag} can be merged cleanly into {branch}...")
    merge_check = run_command(f"git merge --no-commit --no-ff {tag}", check=False)
    
    if merge_check.returncode != 0:
        print(f"Cannot merge {tag} cleanly into {branch}.")
        print("Merge conflicts would occur. Aborting merge.")
        run_command("git merge --abort")
        return False
    
    # Abort the test merge
    run_command("git reset --hard HEAD")
    
    # Now perform the actual merge and push to remote
    print(f"Merging {tag} into {branch}...")
    merge_result = run_command(f"git merge {tag} --no-edit")
    if merge_result.returncode != 0:
        print(f"Failed to merge {tag} into {branch}.")
        return False
    
    print(f"Pushing changes to remote...")
    push_result = run_command(f"git push origin {branch}")
    if push_result.returncode != 0:
        print(f"Failed to push changes to remote.")
        return False
    
    print(f"Successfully merged {tag} into {branch} and pushed to remote.")
    return True


def main():
    parser = argparse.ArgumentParser(
        description="Merge a tag into a branch on a GitHub repository.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s leanprover/mathlib4 stable v4.6.0    Merge tag v4.6.0 into stable branch

The script will:
1. Clone the repository
2. Check if the tag and branch exist
3. Check if the tag can be merged cleanly into the branch
4. Perform the merge and push to remote if possible
        """
    )
    parser.add_argument("repo", help="GitHub repository in the format 'organization/repository'")
    parser.add_argument("branch", help="The target branch to merge into")
    parser.add_argument("tag", help="The tag to merge from")
    
    args = parser.parse_args()
    
    # Create a temporary directory for the repository
    temp_dir = tempfile.mkdtemp()
    try:
        # Clone the repository
        if not clone_repo(args.repo, temp_dir):
            sys.exit(1)
        
        # Check if the tag can be merged and perform the merge
        if not check_and_merge(args.repo, args.branch, args.tag, temp_dir):
            sys.exit(1)
        
    finally:
        # Clean up the temporary directory
        print(f"Cleaning up temporary files...")
        shutil.rmtree(temp_dir)


if __name__ == "__main__":
    main() 