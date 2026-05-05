---
name: release-highlights
description: Write the Highlights section for Lean 4 release notes. Use when asked to write, draft, or update release highlights for a Lean version.
allowed-tools: Bash, Read, Glob, Grep, Edit, Write, WebFetch, WebSearch
---

# Write Release Highlights for Lean

You are writing the "Highlights" section for a Lean 4 release. This section goes at the top of the release notes (after the statistics paragraph) and summarizes the most important changes for users.

## Input

You will be given the release notes file for a Lean version (e.g. `v4.30.0`). This file is a `.lean` file in the `leanprover/reference-manual` repository under `Manual/Releases/`, containing embedded markdown.

**Reference manual repo path:** Before starting, check whether you know the local path to the `leanprover/reference-manual` repository clone. If you don't know it, ask the user for the path. Do not guess or assume a path — the user may have it checked out anywhere.

**Version:** Ask the user which version to write highlights for. Do not assume a version — the user must specify it explicitly (e.g. `v4.30.0`).

The release notes file already contains:
- A statistics paragraph ("For this release, N changes landed...")
- Detailed per-category sections (Language, Library, Tactics, Lake, etc.) with one bullet per PR

Your job is to write a `# Highlights` section to insert between the statistics paragraph and the detailed sections.

## Process

### Step 1: Gather context

1. Read the full release notes file carefully.
2. **Fetch and read ALL PR descriptions** for every PR mentioned in the release notes for the *current* release — no exceptions, no sampling. Use `gh pr view NNNNN --repo leanprover/lean4 --json body` for each one. This includes cross-referenced PRs. Only read the current release's notes file — do NOT also read or fetch PRs from previous releases' notes files. Do not skip PRs that look minor from their one-line entry; the PR description is often the only way to discover that a change is significant. Batch these calls in parallel where possible. This is essential because:
   - PR descriptions often contain examples, motivation, and context not present in the one-line release note entry.
   - Long, human-written PR descriptions are a strong signal that the change is important and highlight-worthy.
   - **Caveat**: If a PR description appears to be AI-generated (signed by Claude, or recognizable AI style with generic phrasing), do NOT treat length as a signal of importance. AI writes detailed descriptions even for minor fixes.
   - **Watch for milestones hiding in terse entries.** Sometimes a single line like "The old compiler has been replaced by the new compiler" or "grind tactic is now available" represents a *huge* milestone that deserves top billing. Don't let a short release note entry cause you to overlook it.
3. Look at the previous release's highlights to understand the current trajectory of features (e.g., was `grind` highlighted last time? Is the module system still experimental?).

### Step 2: Select highlights

**What to highlight:**
- User-facing UX improvements (editor features, error messages, "try this" improvements, go-to-definition) — these should come first, as they affect the most users
- Major new language features (new commands, new syntax, new elaboration capabilities)
- Significant new tactic capabilities (grind, simp, bv_decide, etc.)
- Monadic verification / mvcgen features — these are a key research direction and should be highlighted when present
- Notable performance improvements
- Important breaking changes that users need to know about (migration guidance is valuable)
- New Lake features
- Major library redesigns or new APIs (String overhaul, iterator API, async primitives, new types)

**What NOT to highlight:**
- Individual bug fixes (unless they fix a very prominent issue)
- Internal refactors
- Individual lemma additions
- Small performance tweaks
- Internal API changes
- Features that are still WIP/preparational for future releases (check with context if unsure)
- Changes where the PR description is the only signal of importance and it's AI-generated

**Signals of highlight-worthiness (in rough priority order):**
1. Changes that affect how users write Lean code day-to-day (new syntax, new tactics, editor UX)
2. Long, human-written PR descriptions with examples — the author thought it was important
3. Multiple related PRs addressing the same feature — indicates sustained effort worth showcasing
4. Explicit "breaking change" labels — collect these in a dedicated subsection
5. Features with demo videos or playground links

**Calibrating depth for different feature types:**
- **Flagship features** (e.g., a major tactic getting new capabilities like `grind`): Give these generous space. Use sub-headings (`###`) for each major new capability, include code examples from PR descriptions. The reader should understand what's new and be able to try it. When a feature like `grind` has multiple distinct new capabilities in one release, each deserves its own sub-section with examples. However, if a feature is being *introduced for the first time*, a brief announcement with a link to its documentation may be better than a deep dive — the reference manual is the right place for comprehensive docs, not the release notes.
- **Code examples are essential.** For any feature that can be demonstrated with code, include an example. Pull examples from PR descriptions — authors often include well-crafted demonstrations. A highlight without a code example is much less useful to the reader.
- **Themed groups of PRs** (e.g., "error messages improved", "performance gains"): A brief thematic summary + a list of PR links is sufficient. Do NOT elaborate on each PR individually — just convey the theme and let the reader follow the links if interested.
- **Related breaking changes should be unified into a single narrative.** When multiple PRs address the same underlying issue (e.g., transparency handling changes touching `isDefEq`, `@[implicit_reducible]`, `simp +instances`, and `inferInstanceAs`), present them as one coherent story with a migration guide, NOT as separate highlights. The reader needs to understand the whole picture, not piece it together from fragments.
- **Migration guides are high-value content.** When a breaking change is disruptive, include practical migration advice: `set_option` workarounds, lakefile.toml configuration examples, available porting scripts, and step-by-step guidance. Check PR descriptions thoroughly for migration instructions — they often contain lakefile.toml snippets, helper scripts, and diagnostic commands that are extremely valuable to include verbatim. This is often the most useful part of the highlights for affected users.
- **Experimental features** can be highlighted but should be clearly labeled with "Experimental:" in the heading (e.g., `## Experimental: Module System`). This signals to users that the feature is available for experimentation but not yet stable. Do NOT give experimental features the same prominence as stable features.
- **Policy/process changes** (e.g., backward compatibility options policy): Brief mention, 1-2 sentences.
- **Internal infrastructure** (e.g., symbol clash prevention, try? parallelism, compiler pass migrations): Usually not highlight-worthy unless the user impact is direct and significant (e.g., measurable startup time improvement).

**What NOT to highlight (continued):**
- Internal milestones (e.g., removing old compiler backend) unless they have direct user impact
- Incremental improvements to a feature that was already highlighted in a previous release, unless there's a qualitative leap (e.g., don't re-highlight grind every release just because it got faster; DO highlight when grind gets a fundamentally new capability like interactive mode)
- Many small improvements to the same subsystem — summarize them in the intro paragraph instead of giving them their own section

**How many highlights?**
- The number of highlights should reflect the release. Feature-rich releases (v4.18, v4.22, v4.25) may have 7-13 topics. Consolidation releases (v4.23, v4.24) may have just 2-5 topics.
- **Err on the side of fewer highlights.** A highlight section that's too long fails its purpose — it becomes just another copy of the detailed list. It is better to have 3 really well-written highlights than 10 mediocre ones.
- If the release is light on big features, say so in the intro paragraph (e.g., "brings significant performance improvements, better error messages, and a plethora of bug fixes and consolidations") and only highlight the 2-3 things that are genuinely new to users.
- If nearly everything seems highlight-worthy, you are probably not being selective enough. Step back and ask: "Would a Lean user who skims only this section get the right picture of this release?"
- **Breaking changes** should be collected into a dedicated `## Breaking Changes` subsection at the end of the highlights section. This is more useful to users than scattering breaking changes across feature descriptions. When a breaking change is directly related to a highlighted feature (e.g., String.Slice overhaul), mention it briefly in the feature highlight AND include it with migration details in the Breaking Changes section.

### Step 3: Write the highlights

**Structure:**

```markdown
# Highlights

[Optional 1-3 sentence overview of the release's themes]

## [Descriptive Feature Name]

[#NNNNN](https://github.com/leanprover/lean4/pull/NNNNN) [prose description
of the change, what it does, why it matters].

[Code example if available and illuminating]

## [Flagship Feature with Sub-items] (e.g., "New Features in Grind")

### [Sub-capability 1]

[#NNNNN](...) [description with code example]

### [Sub-capability 2]

[#NNNNN](...) [description with code example]

### Other New Features in [Feature]

- [brief bullet list of smaller items with PR links]

## [Themed Group] (e.g., "Error Messages", "Performance Gains")

[1-2 sentence thematic summary]

PRs: [#N1](...), [#N2](...), [#N3](...).

## Library Highlights

[Thematic summary of library changes, not an exhaustive list.]

## Breaking Changes

- [#NNNNN](...) [description + migration guidance]
- [#NNNNN](...) [description + migration guidance]
```

**Writing style:**
- Technical but accessible. Assume the reader uses Lean but may not follow development closely.
- Third person, declarative: "[#NNNNN] adds support for...", "[#NNNNN] implements..."
- Show excitement about genuine progress — these notes should "show off the hard work that went into the release" — but don't be breathless or use marketing language.
- Include code examples when they help illustrate a feature. Pull good examples from PR descriptions or linked issues.
- For breaking changes, always include migration guidance when available.
- Keep individual highlight entries concise (1-3 paragraphs typically). For major features, more detail is fine.

**Formatting rules:**
- PR links are always full markdown links: `[#NNNNN](https://github.com/leanprover/lean4/pull/NNNNN)`
- Issue links similarly: `[#NNNN](https://github.com/leanprover/lean4/issues/NNNN)`
- Use `## ` for each major highlight topic heading
- Use `### ` for sub-topics within a highlight (e.g., multiple grind features under `## New Features in Grind`)
- Code blocks use triple backticks. Use `lean` language tag when appropriate for Verso-native files, plain triple backticks for markdown-block files.
- Breaking changes are marked with `*Breaking change:*` or `*Breaking Changes:*` in italic
- When consolidating multiple PRs into one highlight, list all PR links

**Regarding the detailed sections below the highlights:**
- Do NOT reorder or restructure the detailed per-category sections
- If a PR was moved to highlights with extended description, optionally add a brief note in the detailed section: "see highlights for details"
- All PRs should remain in the detailed list even if highlighted above

### Step 4: Library highlights

Library changes deserve a `## Library Highlights` subsection only when there are genuinely notable library changes (new types, API redesigns, new frameworks). The approach:
- Do NOT try to list every library change — that would just duplicate the detailed list
- Summarize thematically: "expanded lemmas for Array/Vector/List", "better support for bitwise operations"
- Highlight genuinely new types, major API redesigns, or new frameworks (e.g., async primitives, iterator API)
- Call out breaking library changes explicitly
- If library changes are mostly incremental lemma additions and minor fixes, omit this subsection entirely or mention them in the intro paragraph

### Step 5: Review

Before finalizing, check:
- [ ] Is the highlights section between the statistics paragraph and the first detailed section?
- [ ] Are all PR links correctly formatted?
- [ ] Does each highlight actually add value over the one-line entry in the detailed list?
- [ ] Are breaking changes clearly called out with migration guidance?
- [ ] Is the length appropriate? (Not so long it's just a copy of the detailed list, not so short it misses important things)
- [ ] Does it sound exciting and professional without being over-the-top?
- [ ] Are WIP/preparational features excluded (or marked as experimental/preview)?

### Step 6: Post-processing — Link to the reference manual

After writing the highlights, do a post-processing pass to add cross-references to the Lean reference manual where relevant. This requires using **Verso-native format** (not markdown blocks).

Use Verso cross-reference syntax:
- `{tactic}\`grind\`` — links to a tactic's documentation
- `{name}\`String.Slice\`` — links to a declaration's documentation
- `{option}\`backward.do.legacy\`` — links to an option's documentation
- `{ref "section-slug"}[display text]` — links to a named section
- `{keywordOf Lean.Parser.Command.grind_pattern}\`grind_pattern\`` — links to a keyword

Examples of where to add these:
- When mentioning a tactic by name, use `{tactic}\`tacticName\``
- When mentioning a type or definition, use `{name}\`Fully.Qualified.Name\``
- When mentioning an option, use `{option}\`option.name\``
- When referring to a documented section of the reference manual, use `{ref "slug"}[text]`

To find valid section slugs, search the reference manual source for `tag :=` or section headings. Do not guess slugs — only use ones you can verify exist.

This step does not affect highlight selection or phrasing — it just enriches the output with useful navigation links.

## Format details

Always use **Verso-native format**: markdown is written directly in the `#doc` block. Use `# Highlights` as the heading level, `## ` for topics, `### ` for sub-topics.

Code blocks within Verso-native files use ` ```lean ` (with language tag) when the code should be checked by Lean, or plain ` ``` ` when it should not be checked (e.g., illustrative goal states, pseudo-code).
