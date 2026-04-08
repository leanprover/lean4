# Release Management Command

Execute the release process for a given version by running the release checklist and following its instructions.

## Before Starting

**IMPORTANT**: Before beginning the release process, read the in-file documentation:
- Read `script/release_checklist.py` for what the checklist script does
- Read `script/release_steps.py` for what the release steps script does

These comments explain the scripts' behavior, which repositories get special handling, and how errors are handled.

## Arguments
- `version`: The version to release (e.g., v4.24.0)

## Release Notes (Required for -rc1 releases)

For first release candidates (`-rc1`), you must create release notes BEFORE the reference-manual toolchain bump PR can be merged.

**Steps to create release notes:**

1. Generate the release notes:
   ```bash
   cd /path/to/lean4
   python3 script/release_notes.py --since <previous_version> > /tmp/release-notes-<version>.md
   ```
   Replace `<previous_version>` with the last stable release (e.g., `v4.27.0` when releasing `v4.28.0-rc1`).

2. Review `/tmp/release-notes-<version>.md` for common issues:
   - **Unterminated code blocks**: Look for code fences that aren't closed. Fetch original PR with `gh pr view <number>` to repair.
   - **Truncated descriptions**: Some may end mid-sentence. Complete them from the original PR.
   - **Markdown issues**: Other syntax problems that could cause parsing errors.

3. Create the release notes file in the reference-manual repository:
   - File path: `Manual/Releases/v<version>.lean` (e.g., `v4_28_0.lean`)
   - Use Verso format with proper imports and `#doc (Manual)` block
   - **Use `#` for headers, not `##`** (Verso uses level 1 for subsections)
   - **Use plain ` ``` ` not ` ```lean `** (the latter executes code)
   - **Wrap underscore identifiers in backticks**: `` `bv_decide` `` not `bv_decide`

4. Update `Manual/Releases.lean`:
   - Add import: `import Manual.Releases.«v4_28_0»`
   - Add include: `{include 0 Manual.Releases.«v4_28_0»}`

5. Build to verify: `lake build Manual.Releases.v4_28_0`

6. Create a **separate PR** for release notes (not bundled with toolchain bump):
   ```bash
   git checkout -b v<version>-release-notes
   gh pr create --title "doc: add v<version> release notes"
   ```

For subsequent RCs (`-rc2`, etc.) and stable releases, just update the version number in the existing release notes file title.

See `doc/dev/release_checklist.md` section "Writing the release notes" for full details.

## Process

1. Run `script/release_checklist.py {version}` to check the current status
2. **CRITICAL: If preliminary lean4 checks fail, STOP immediately and alert the user**
   - Check for: release branch exists, CMake version correct, tag exists, release page exists, release notes file exists
   - **IMPORTANT**: The release page is created AUTOMATICALLY by CI after pushing the tag - DO NOT create it manually
   - **IMPORTANT**: For -rc1 releases, release notes must be created before proceeding
   - Do NOT create any PRs or proceed with repository updates if these checks fail
3. Create a todo list tracking all repositories that need updates
4. **CRITICAL RULE: You can ONLY run `release_steps.py` for a repository if `release_checklist.py` explicitly says to do so**
   - The checklist output will say "Run `script/release_steps.py {version} {repo_name}` to create it"
   - If a repository shows "🟡 Dependencies not ready", you CANNOT create a PR for it yet
   - You MUST rerun `release_checklist.py` before attempting to create PRs for any new repositories
5. For each repository that the checklist says needs updating:
   - Run `script/release_steps.py {version} {repo_name}` to create the PR
   - Mark it complete when the PR is created
6. After creating PRs, notify the user which PRs need review and merging
7. **MANDATORY: Rerun `release_checklist.py` to check current status**
   - Do this after creating each batch of PRs
   - Do this after the user reports PRs have been merged
   - NEVER assume a repository is ready without checking the checklist output
8. As PRs are merged and tagged, dependent repositories will become ready
9. Continue the cycle: run checklist → create PRs for ready repos → wait for merges → repeat
10. Continue until all repositories are updated and the release is complete

## Important Notes

- **NEVER merge PRs autonomously** - always wait for the user to merge PRs themselves
- The `release_steps.py` script is idempotent - it's safe to rerun
- The `release_checklist.py` script is idempotent - it's safe to rerun
- Some repositories depend on others (e.g., mathlib4 depends on batteries, aesop, etc.)
- Wait for user to merge PRs before dependent repos can be updated
- Alert user if anything unusual or scary happens
- Use appropriate timeouts for long-running builds (verso can take 10+ minutes)
- ProofWidgets4 uses semantic versioning (v0.0.X) - it's okay to create and push the next sequential tag yourself when needed for a release

## PR Status Reporting

Every time you run `release_checklist.py`, you MUST:
1. Parse the output to identify ALL open PRs mentioned (lines with "✅ PR with title ... exists")
2. Provide a summary to the user listing ALL open PRs that need review
3. Group them by status:
   - PRs for repositories that are blocked by dependencies (show these but note they're blocked)
   - PRs for repositories that are ready to merge (highlight these)
4. Format the summary clearly with PR numbers and URLs

This summary should be provided EVERY time you run the checklist, not just after creating new PRs.
The user needs to see the complete picture of what's waiting for review.

## Checking PR Status When Asked

When the user asks for "status" or you need to report on PRs between checklist runs:
- **ALWAYS check actual PR state** using `gh pr view <number> --repo <repo> --json state,mergedAt`
- Do NOT rely on cached CI results or previous checklist output
- The user may have merged PRs since your last check
- Report which PRs are MERGED, which are OPEN with CI status, and which are still pending
- After discovering merged PRs, rerun `release_checklist.py` to advance the release process

## Nightly Infrastructure

The nightly build system uses branches and tags across two repositories:

- `leanprover/lean4` has **branches** `nightly` and `nightly-with-mathlib` tracking the latest nightly builds
- `leanprover/lean4-nightly` has **dated tags** like `nightly-2026-01-23`

When a nightly succeeds with mathlib, all three should point to the same commit. Don't confuse these: branches are in the main lean4 repo, dated tags are in lean4-nightly.

## CI Failures: Investigate Immediately

**CRITICAL: If the checklist reports `❌ CI: X check(s) failing` for any PR, investigate immediately.**

Do NOT:
- Report it as "CI in progress" or "some checks pending"
- Wait for the remaining checks to finish before investigating
- Assume it's a transient failure without checking

DO:
1. Run `gh pr checks <number> --repo <owner>/<repo>` to see which specific check failed
2. Run `gh run view <run-id> --repo <owner>/<repo> --log-failed` to see the failure output
3. Diagnose the failure and report clearly to the user: what failed and why
4. Propose a fix if one is obvious (e.g., subverso version mismatch, transient elan install error)

The checklist now distinguishes `❌ X check(s) failing, Y still in progress` from `🔄 Y check(s) in progress`.
Any `❌` in CI status requires immediate investigation — do not move on.

## Waiting for CI or Merges

Use `gh pr checks --watch` to block until a PR's CI checks complete (no polling needed).
Run these as background bash commands so you get notified when they finish:

```bash
# Watch CI, then check merge state
gh pr checks <number> --repo <owner>/<repo> --watch && gh pr view <number> --repo <owner>/<repo> --json state --jq '.state'
```

For multiple PRs, launch one background command per PR in parallel. When each completes,
you'll be notified automatically via a task-notification. Do NOT use sleep-based polling
loops — `--watch` is event-driven and exits as soon as checks finish.

Note: `gh pr checks --watch` exits as soon as ALL checks complete (pass or fail). If some checks
fail while others are still running, `--watch` will continue until everything settles, then exit
with a non-zero code. So a background `--watch` finishing = all checks done; check which failed.

## Mathlib Bump Branches

Mathlib `bump/v4.X.0` branches live on the **fork** `leanprover-community/mathlib4-nightly-testing`,
NOT on `leanprover-community/mathlib4`.

## Never Force-Update Remote Refs Without Confirmation

Never force-update an existing remote branch or tag via `git push --force` or the GitHub API
without explicit user confirmation.

## Error Handling

**CRITICAL**: If something goes wrong or a command fails:
- **DO NOT** try to manually reproduce the failing steps yourself
- **DO NOT** try to fix things by running git commands or other manual operations
- Both scripts are idempotent and designed to handle partial completion gracefully
- If a script continues to fail after retrying, report the error to the user and wait for instructions
