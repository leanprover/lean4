#!/usr/bin/env python3

"""
Execute release steps for Lean4 repositories.

This script helps automate the release process for Lean4 and its dependent repositories
by actually executing the step-by-step instructions for updating toolchains, creating tags,
and managing branches.

Usage:
    python3 release_steps.py <version> <repo>

Arguments:
    version: The version to set in the lean-toolchain file (e.g., v4.6.0)
    repo: The repository name as specified in release_repos.yml

Example:
    python3 release_steps.py v4.6.0 mathlib4
    python3 release_steps.py v4.6.0 batteries

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
import subprocess
import shutil
import json
from pathlib import Path

# Color functions for terminal output
def blue(text):
    """Blue text for 'I'm doing something' messages."""
    return f"\033[94m{text}\033[0m"

def green(text):
    """Green text for 'successful step' messages."""
    return f"\033[92m{text}\033[0m"

def red(text):
    """Red text for 'this looks bad' messages."""
    return f"\033[91m{text}\033[0m"

def yellow(text):
    """Yellow text for warnings."""
    return f"\033[93m{text}\033[0m"

def run_command(cmd, cwd=None, check=True, stream_output=False):
    """Run a shell command and return the result."""
    print(blue(f"Running: {cmd}"))
    try:
        if stream_output:
            # Stream output in real-time for long-running commands
            result = subprocess.run(cmd, shell=True, cwd=cwd, check=check, text=True)
            return result
        else:
            # Capture output for commands where we need to process the result
            result = subprocess.run(cmd, shell=True, cwd=cwd, check=check, 
                                  capture_output=True, text=True)
            if result.stdout:
                # Command output in plain white (default terminal color)
                print(result.stdout)
            return result
    except subprocess.CalledProcessError as e:
        print(red(f"Error running command: {cmd}"))
        print(red(f"Exit code: {e.returncode}"))
        if not stream_output:
            print(f"Stdout: {e.stdout}")
            print(f"Stderr: {e.stderr}")
        raise

def load_repos_config(file_path):
    with open(file_path, "r") as f:
        return yaml.safe_load(f)["repositories"]

def find_repo(repo_name, config):
    matching_repos = [r for r in config if r["name"] == repo_name]
    if not matching_repos:
        print(red(f"Error: No repository named '{repo_name}' found in configuration."))
        available_repos = [r["name"] for r in config]
        print(yellow(f"Available repositories: {', '.join(available_repos)}"))
        sys.exit(1)
    return matching_repos[0]

def setup_downstream_releases_dir():
    """Create the downstream_releases directory if it doesn't exist."""
    downstream_dir = Path("downstream_releases")
    if not downstream_dir.exists():
        print(blue(f"Creating {downstream_dir} directory..."))
        downstream_dir.mkdir()
        print(green(f"Created {downstream_dir} directory"))
    return downstream_dir

def clone_or_update_repo(repo_url, repo_dir, downstream_dir):
    """Clone the repository if it doesn't exist, or update it if it does."""
    repo_path = downstream_dir / repo_dir
    
    if repo_path.exists():
        print(blue(f"Repository {repo_dir} already exists, updating..."))
        run_command("git fetch", cwd=repo_path)
        print(green(f"Updated repository {repo_dir}"))
    else:
        print(blue(f"Cloning {repo_url} to {repo_path}..."))
        run_command(f"git clone {repo_url}", cwd=downstream_dir)
        print(green(f"Cloned repository {repo_dir}"))
    
    return repo_path

def get_remotes_for_repo(repo_name):
    """Get the appropriate remotes for bump and nightly-testing branches based on repository."""
    if repo_name == "mathlib4":
        return "nightly-testing", "nightly-testing"
    else:
        return "origin", "origin"

def execute_release_steps(repo, version, config):
    repo_config = find_repo(repo, config)
    repo_name = repo_config['name']
    repo_url = repo_config['url']
    # Extract the last component of the URL, removing the .git extension if present
    repo_dir = repo_url.split('/')[-1].replace('.git', '')
    default_branch = repo_config.get("branch", "main")
    dependencies = repo_config.get("dependencies", [])
    requires_tagging = repo_config.get("toolchain-tag", True)
    has_stable_branch = repo_config.get("stable-branch", True)

    # Setup downstream releases directory
    downstream_dir = setup_downstream_releases_dir()
    
    # Clone or update the repository
    repo_path = clone_or_update_repo(repo_url, repo_dir, downstream_dir)
    
    # Special remote setup for mathlib4
    if repo_name == "mathlib4":
        print(blue("Setting up special remotes for mathlib4..."))
        try:
            # Check if nightly-testing remote already exists
            result = run_command("git remote get-url nightly-testing", cwd=repo_path, check=False)
            if result.returncode != 0:
                # Add the nightly-testing remote
                run_command("git remote add nightly-testing https://github.com/leanprover-community/mathlib4-nightly-testing.git", cwd=repo_path)
                print(green("Added nightly-testing remote"))
            else:
                print(green("nightly-testing remote already exists"))
            
            # Fetch from the nightly-testing remote
            run_command("git fetch nightly-testing", cwd=repo_path)
            print(green("Fetched from nightly-testing remote"))
        except subprocess.CalledProcessError as e:
            print(red(f"Error setting up mathlib4 remotes: {e}"))
            print(yellow("Continuing with default remote setup..."))
    
    print(blue(f"\n=== Executing release steps for {repo_name} ==="))
    
    # Execute the release steps
    run_command(f"git checkout {default_branch} && git pull", cwd=repo_path)
    
    # Special rc1 safety check for batteries and mathlib4 (before creating any branches)
    if re.search(r'rc\d+$', version) and repo_name in ["batteries", "mathlib4"] and version.endswith('-rc1'):
        print(blue("This repo has nightly-testing infrastructure"))
        print(blue(f"Checking if nightly-testing can be safely merged into bump/{version.split('-rc')[0]}..."))
        
        # Get the base version (e.g., v4.6.0 from v4.6.0-rc1)
        base_version = version.split('-rc')[0]
        bump_branch = f"bump/{base_version}"
        
        # Determine which remote to use for bump and nightly-testing branches
        bump_remote, nightly_remote = get_remotes_for_repo(repo_name)
        
        try:
            # Fetch latest changes from the appropriate remote
            run_command(f"git fetch {bump_remote}", cwd=repo_path)
            
            # Check if the bump branch exists
            result = run_command(f"git show-ref --verify --quiet refs/remotes/{bump_remote}/{bump_branch}", cwd=repo_path, check=False)
            if result.returncode != 0:
                print(red(f"Bump branch {bump_remote}/{bump_branch} does not exist. Cannot perform safety check."))
                print(yellow("Please ensure the bump branch exists before proceeding."))
                return
            
            # Create a temporary branch for testing the merge
            temp_branch = f"temp-merge-test-{base_version}"
            run_command(f"git checkout -b {temp_branch} {bump_remote}/{bump_branch}", cwd=repo_path)
            
            # Try to merge nightly-testing
            try:
                run_command(f"git merge {nightly_remote}/nightly-testing", cwd=repo_path)
                
                # Check what files have changed compared to the bump branch
                changed_files = run_command(f"git diff --name-only {bump_remote}/{bump_branch}..HEAD", cwd=repo_path)
                
                # Filter out allowed changes
                allowed_patterns = ['lean-toolchain', 'lake-manifest.json']
                problematic_files = []
                
                for file in changed_files.stdout.strip().split('\n'):
                    if file.strip():  # Skip empty lines
                        is_allowed = any(pattern in file for pattern in allowed_patterns)
                        if not is_allowed:
                            problematic_files.append(file)
                
                # Clean up temporary branch and return to default branch
                run_command(f"git checkout {default_branch}", cwd=repo_path)
                run_command(f"git branch -D {temp_branch}", cwd=repo_path)
                
                if problematic_files:
                    print(red("❌ Safety check failed!"))
                    print(red(f"Merging nightly-testing into {bump_branch} would result in changes to:"))
                    for file in problematic_files:
                        print(red(f"  - {file}"))
                    print(yellow("\nYou need to make a PR merging the changes from nightly-testing into the bump branch first."))
                    print(yellow(f"Create a PR from nightly-testing targeting {bump_branch} to resolve these conflicts."))
                    return
                else:
                    print(green("✅ Safety check passed - only lean-toolchain and/or lake-manifest.json would change"))
                    
            except subprocess.CalledProcessError:
                # Clean up temporary branch on merge failure
                run_command(f"git checkout {default_branch}", cwd=repo_path)
                run_command(f"git branch -D {temp_branch}", cwd=repo_path)
                print(red("❌ Safety check failed!"))
                print(red(f"Merging nightly-testing into {bump_branch} would result in merge conflicts."))
                print(yellow("\nYou need to make a PR merging the changes from nightly-testing into the bump branch first."))
                print(yellow(f"Create a PR from nightly-testing targeting {bump_branch} to resolve these conflicts."))
                return
                
        except subprocess.CalledProcessError as e:
            # Ensure we're back on the default branch even if setup failed
            try:
                run_command(f"git checkout {default_branch}", cwd=repo_path)
            except subprocess.CalledProcessError:
                print(red(f"Cannot return to {default_branch} branch. Repository is in an inconsistent state."))
                print(red("Please manually check the repository state and fix any issues."))
                return
            print(red(f"Error during safety check: {e}"))
            print(yellow("Skipping safety check and proceeding with normal merge..."))
    
    # Check if the branch already exists
    branch_name = f"bump_to_{version}"
    try:
        # Check if branch exists locally
        result = run_command(f"git show-ref --verify --quiet refs/heads/{branch_name}", cwd=repo_path, check=False)
        if result.returncode == 0:
            print(blue(f"Branch {branch_name} already exists, checking it out..."))
            run_command(f"git checkout {branch_name}", cwd=repo_path)
            print(green(f"Checked out existing branch {branch_name}"))
        else:
            print(blue(f"Creating new branch {branch_name}..."))
            run_command(f"git checkout -b {branch_name}", cwd=repo_path)
            print(green(f"Created new branch {branch_name}"))
    except subprocess.CalledProcessError:
        print(blue(f"Creating new branch {branch_name}..."))
        run_command(f"git checkout -b {branch_name}", cwd=repo_path)
        print(green(f"Created new branch {branch_name}"))
    
    # Update lean-toolchain
    print(blue("Updating lean-toolchain file..."))
    toolchain_file = repo_path / "lean-toolchain"
    with open(toolchain_file, "w") as f:
        f.write(f"leanprover/lean4:{version}\n")
    print(green(f"Updated lean-toolchain to leanprover/lean4:{version}"))

    # Special cases for specific repositories
    if repo_name == "repl":
        run_command("lake update", cwd=repo_path, stream_output=True)
        mathlib_test_dir = repo_path / "test" / "Mathlib"
        run_command(f'perl -pi -e \'s/rev = "v\\d+\\.\\d+\\.\\d+(-rc\\d+)?"/rev = "{version}"/g\' lakefile.toml', cwd=mathlib_test_dir)
        
        # Update lean-toolchain in test/Mathlib
        print(blue("Updating test/Mathlib/lean-toolchain..."))
        mathlib_toolchain = mathlib_test_dir / "lean-toolchain"
        with open(mathlib_toolchain, "w") as f:
            f.write(f"leanprover/lean4:{version}\n")
        print(green(f"Updated test/Mathlib/lean-toolchain to leanprover/lean4:{version}"))
        
        run_command("lake update", cwd=mathlib_test_dir, stream_output=True)
        try:
            result = run_command("./test.sh", cwd=repo_path, stream_output=True, check=False)
            if result.returncode == 0:
                print(green("Tests completed successfully"))
            else:
                print(red("Tests failed, but continuing with PR creation..."))
                print(red(f"Test exit code: {result.returncode}"))
        except subprocess.CalledProcessError as e:
            print(red("Tests failed, but continuing with PR creation..."))
            print(red(f"Test error: {e}"))
    elif dependencies:
        run_command(f'perl -pi -e \'s/"v4\\.[0-9]+(\\.[0-9]+)?(-rc[0-9]+)?"/"' + version + '"/g\' lakefile.*', cwd=repo_path)
        run_command("lake update", cwd=repo_path, stream_output=True)

    # Commit changes (only if there are changes)
    print(blue("Checking for changes to commit..."))
    try:
        # Check if there are any changes to commit (staged or unstaged)
        result = run_command("git status --porcelain", cwd=repo_path, check=False)
        if result.stdout.strip():  # There are changes
            print(blue("Committing changes..."))
            run_command(f'git commit -am "chore: bump toolchain to {version}"', cwd=repo_path)
            print(green(f"Committed changes: chore: bump toolchain to {version}"))
        else:
            print(green("No changes to commit - toolchain already up to date"))
    except subprocess.CalledProcessError:
        print(yellow("Failed to check for changes, attempting commit anyway..."))
        try:
            run_command(f'git commit -am "chore: bump toolchain to {version}"', cwd=repo_path)
        except subprocess.CalledProcessError as e:
            if "nothing to commit" in e.stderr:
                print(green("No changes to commit - toolchain already up to date"))
            else:
                raise

    # Handle special merging cases
    if re.search(r'rc\d+$', version) and repo_name in ["batteries", "mathlib4"]:
        print(blue("This repo has nightly-testing infrastructure"))
        
        # Determine which remote to use for bump branches
        bump_remote, nightly_remote = get_remotes_for_repo(repo_name)
        
        try:
            print(blue(f"Merging {bump_remote}/bump/{version.split('-rc')[0]}..."))
            run_command(f"git merge {bump_remote}/bump/{version.split('-rc')[0]}", cwd=repo_path)
            print(green("Merge completed successfully"))
        except subprocess.CalledProcessError:
            print(red("Merge conflicts detected. Please resolve them manually."))
            return
    
    if re.search(r'rc\d+$', version) and repo_name in ["verso", "reference-manual"]:
        print(yellow("This repo does development on nightly-testing: remember to rebase merge the PR."))
        try:
            print(blue("Merging origin/nightly-testing..."))
            run_command("git merge origin/nightly-testing", cwd=repo_path)
            print(green("Merge completed successfully"))
        except subprocess.CalledProcessError:
            print(red("Merge conflicts detected. Please resolve them manually."))
            return

    # Build and test (skip for Mathlib)
    if repo_name not in ["Mathlib", "mathlib4"]:
        print(blue("Building project..."))
        try:
            run_command("lake build", cwd=repo_path, stream_output=True)
            print(green("Build completed successfully"))
        except subprocess.CalledProcessError as e:
            print(red("Build failed, but continuing with PR creation..."))
            print(red(f"Build error: {e}"))
        
        # Check if lake check-test exists before running tests
        print(blue("Running tests..."))
        check_test_result = run_command("lake check-test", cwd=repo_path, check=False)
        if check_test_result.returncode == 0:
            try:
                run_command("lake test", cwd=repo_path, stream_output=True)
                print(green("Tests completed successfully"))
            except subprocess.CalledProcessError as e:
                print(red("Tests failed, but continuing with PR creation..."))
                print(red(f"Test error: {e}"))
        else:
            print(yellow("lake check-test reports that there is no test suite"))

    # Push the branch to remote before creating PR
    print(blue("Checking remote branch status..."))
    try:
        # Check if branch exists on remote
        result = run_command(f"git ls-remote --heads origin {branch_name}", cwd=repo_path, check=False)
        if not result.stdout.strip():
            print(blue(f"Pushing branch {branch_name} to remote..."))
            run_command(f"git push -u origin {branch_name}", cwd=repo_path)
            print(green(f"Successfully pushed branch {branch_name} to remote"))
        else:
            print(blue(f"Branch {branch_name} already exists on remote, pushing any new commits..."))
            run_command(f"git push", cwd=repo_path)
            print(green("Successfully pushed commits to remote"))
    except subprocess.CalledProcessError:
        print(red("Failed to push branch to remote. Please check your permissions and network connection."))
        print(yellow(f"You may need to run: git push -u origin {branch_name}"))
        return

    # Create pull request (only if one doesn't already exist)
    print(blue("Checking for existing pull request..."))
    try:
        # Check if PR already exists for this branch
        result = run_command(f'gh pr list --head {branch_name} --json number', cwd=repo_path, check=False)
        if result.returncode == 0 and result.stdout.strip() != "[]":
            print(green(f"Pull request already exists for branch {branch_name}"))
            # Get the PR URL
            pr_result = run_command(f'gh pr view {branch_name} --json url', cwd=repo_path, check=False)
            if pr_result.returncode == 0:
                pr_data = json.loads(pr_result.stdout)
                print(green(f"PR URL: {pr_data.get('url', 'N/A')}"))
        else:
            # Create new PR
            print(blue("Creating new pull request..."))
            run_command(f'gh pr create --title "chore: bump toolchain to {version}" --body ""', cwd=repo_path)
            print(green("Pull request created successfully!"))
    except subprocess.CalledProcessError:
        print(red("Failed to check for existing PR or create new PR."))
        print(yellow("This could be due to:"))
        print(yellow("1. GitHub CLI not authenticated"))
        print(yellow("2. No push permissions to the repository"))
        print(yellow("3. Network issues"))
        print(f"Branch: {branch_name}")
        print(f"Title: chore: bump toolchain to {version}")
        print(yellow("Please create the PR manually if needed."))

def main():
    parser = argparse.ArgumentParser(
        description="Execute release steps for Lean4 repositories.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s v4.6.0 mathlib4   Execute steps for updating Mathlib to v4.6.0
  %(prog)s v4.6.0 batteries  Execute steps for updating Batteries to v4.6.0
  
The script will:
1. Create a downstream_releases/ directory
2. Clone or update the target repository
3. Update the lean-toolchain file
4. Create appropriate branches and commits
5. Build and test the project
6. Create pull requests

(Note that the steps of creating toolchain version tags, and merging these into `stable` branches,
are handled by `script/release_checklist.py`.)
"""
    )
    parser.add_argument("version", help="The version to set in the lean-toolchain file (e.g., v4.6.0)")
    parser.add_argument("repo", help="The repository name as specified in release_repos.yml")
    args = parser.parse_args()

    config_path = os.path.join(os.path.dirname(__file__), "release_repos.yml")
    config = load_repos_config(config_path)

    execute_release_steps(args.repo, args.version, config)

if __name__ == "__main__":
    main()
