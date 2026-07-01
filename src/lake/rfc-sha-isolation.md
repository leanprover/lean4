### Proposal

`lake cache get` walks git history to the nearest cached ancestor when the current commit has no cache ([`Main.lean:574-589`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/CLI/Main.lean#L574-L589)). For a low-trust source such as fork-PR artifacts, that walk breaks isolation: a build can be served a different commit's cache. This RFC adds a per-service `revDiscovery` policy so a service can be pinned to the current commit's mapping, with no walk, giving the invariant "gets are isolated by SHA" — safe by default and without a per-call flag.

#### Background: cache poisoning and trust segregation

A cache writable by low-trust jobs (e.g., PR CI with arbitrary elaboration code) is open to poisoning: a malicious build publishes an input→output mapping and corrupted artifact. Lake content-addresses artifacts and verifies hashes on download ([`Cache.lean:553-561`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/Config/Cache.lean#L553-L561), [`778-783`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/Config/Cache.lean#L778-L783)), which protects transfer integrity but not mapping authenticity.

One line of defense is to segregate writes by trust level into separate endpoints/scopes, enforced by storage credentials (S3/OIDC). Consumers can then choose to consume from the different endpoints according to different situations.

#### Motivating use case

`mathlib4` has restructured its build cache this way; see [leanprover-community/mathlib4#40035](https://github.com/leanprover-community/mathlib4/pull/40035). Trust-segregated containers (`master`, `forks`, others), each with its own write credentials, read through an ordered fallback chain with per-commit scoping.

For fork artifacts it enforces a per-SHA isolation invariant: a build is only served the cache of the specific commit it is on, so a closed or hidden PR's artifacts cannot be served to a later honest PR. This RFC brings that invariant to `lake cache`.

#### The invariant: gets isolated by SHA

Content-addressing already pins artifact integrity ([`Cache.lean:778-783`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/Config/Cache.lean#L778-L783)): whatever endpoint serves a hash, the bytes must match it or are rejected. So the only thing that decides what a build consumes is which mapping it reads. A mapping is `{rev}.jsonl`, keyed by commit SHA, and SHAs are globally unique. Reading only the current commit's mapping binds consumption to that commit's vouched outputs; a different or closed PR's mapping is a file you never fetch. The unbounded walk to an ancestor is exactly what breaks this, so the fix is to not walk.

#### Current state

`cache get --rev <sha>` already fetches exactly that rev's mapping with no walk, erroring if absent ([`Main.lean:535-538`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/CLI/Main.lean#L535-L538)). But it must be passed on every call, and for a custom S3 service it also requires `--scope`/`--repo` ([`Main.lean:565-566`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/CLI/Main.lean#L565-L566)). With no `--rev`, the default is to walk ([`Main.lean:574-589`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/CLI/Main.lean#L574-L589)).

#### The change

Per-service `revDiscovery`:

- `nearest`: walk ancestors, take the first revision cached. (current behavior, default)
- `head`: current commit only, no walk. Enforces SHA isolation.

A service marked `revDiscovery = "head"` makes a bare `lake cache get` against it isolated by default, with no `--rev` to remember and no SHA to compute.

#### Scope is not needed for read isolation

Read isolation does not need scope. The mapping is `{rev}.jsonl`, keyed by commit SHA, and SHAs are globally unique, so choosing the mapping (via `revDiscovery`) already fixes which build is trusted; the artifacts it names are content-addressed and hash-verified. Per-commit or per-repo artifact prefixes (e.g., Mathlib's `/f/{repo}/{sha}/{hash}.art`) add nothing on reads, and fragment reuse: a delta built at commit C lands under `/{C}/`, so a later commit reusing it looks under `/{C2}/` and misses it.

Scope is therefore a publish-side concern (write-IAM path isolation, GC), not a read input. Tiers are already separated by service (bucket); with a write-once forks bucket, artifacts and mappings can be stored flat and `cache get` needs no scope. Where a layout does use a prefix, the tier carries a fixed `scope` string that `get` mirrors, with no git derivation and no `scopeMode`. Exposing `scope` as a config field, so a flat S3 service needs no `--scope` flag, is a separate proposal; see the scope-config RFC.

#### Configuration sketch

```toml
[[cache.service]]
name = "forks"
kind = "s3"
artifactEndpoint = "https://…/forks/artifacts"
revisionEndpoint = "https://…/forks/revisions"
revDiscovery = "head"            # only the current commit's mapping; no walk
```

`lake cache get --service forks` then fetches only the current commit's mapping and the artifacts it names, all hash-verified.

#### Interaction with other flags

- `--max-revs` (walk depth) does not loosen `head`. A `head` service never walks, so the flag is ignored with a warning rather than restoring the walk. This fails safe — the SHA-isolation invariant cannot be silently disabled by a stray CLI flag — and composes with the read-chain RFC, where `--max-revs` bounds the `nearest` legs of a chain and is ignored for `head` ones (a warning, not an error, so it need not apply uniformly). A deliberate per-call override can be added in a future revision if a concrete need appears.
- `--fail-level` (`--wfail`/`--iofail`) escalates that warning like any other: by default the ignored `--max-revs` is a warning, and under `--wfail` it is a hard failure, so strict callers get an error without `head` needing one.
- `--rev <sha>` is orthogonal and unchanged: it already pins one revision with no walk, so it is consistent with `head` and fixes the revision for that call regardless of policy.
- An explicit mappings file (`lake cache get <file>`) bypasses revision discovery entirely, so `revDiscovery` does not apply; the mapping is read from the file as given.

`--service` selects which service's policy applies; `--scope`/`--repo`, `--platform`/`--toolchain`, `--mappings-only`, and `--force-download` are independent of `revDiscovery`.

#### Security

The trust boundary preventing poisoning is publish-side: which endpoint a job can write to, enforced by CI credentials and storage IAM (e.g., only `master` CI holds the `master` key). `cache put` and write-credential handling ([`Main.lean:591-619`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/CLI/Main.lean#L591-L619)) are unchanged.

On the read side, `revDiscovery = "head"` is the mechanism for the SHA invariant: the build reads only the current commit's mapping, so a low-trust source can only serve the build of the exact commit it is on. Artifacts are verified against their content hash regardless of endpoint, so the mapping source is the only thing that must be trusted (or head-pinned).

#### Alternatives considered

- Per-call `--rev <sha>` (status quo): the no-walk mechanism exists ([`Main.lean:535-538`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/CLI/Main.lean#L535-L538)) but is flag-dependent — a forgetful caller or a bare `lake cache get` still walks — and it currently requires `--scope`. This RFC makes it a safe-by-default per-service policy.
- Strict `head` vs a bounded window: `mathlib4` accepts the most recent cached commit within `--unsafe-window` (default 1) rather than strictly HEAD. A bounded window matches its hit-rate while staying isolated; strict `head` is simpler and stricter.
- Per-commit/per-repo artifact path scoping (`mathlib4`'s `/f/{repo}/{sha}/{hash}.art`). Redundant for read isolation, which the SHA-keyed mapping already provides, and it fragments cross-commit reuse. It remains useful publish-side (write-IAM, GC).

#### Open questions

- Default behavior of `head`: strictly the current commit, or a small bounded window over cached commits.

#### Backwards compatibility

Additive. `revDiscovery` defaults to `nearest`, today's behavior. `head` is opt-in per service; existing flags including `--rev` are unaffected.

#### User Experience

A service is marked no-walk once in config, so a bare `lake cache get` against it is SHA-isolated. The caller does not remember `--rev`, compute a SHA, or pass a scope.

#### Beneficiaries

Projects that consume low-trust (fork/PR) caches and need the assurance that a build only sees its own commit's artifacts. Immediate driver: `mathlib4`'s migration of its multi-container cache (leanprover-community/mathlib4#40035) to `lake cache`, which needs this invariant for fork fetches.

#### Maintainability

Small surface. `revDiscovery = "nearest"` is the existing walk; `head` reuses the existing no-walk `--rev` path. No new transport or storage.

### Community Feedback

Not yet discussed on Zulip. I will open a thread on #lake and summarize and link it here. Input wanted from the cache subsystem authors and from projects maintaining their own caches.

### Impact

Add :+1: to [issues you consider important](https://github.com/leanprover/lean4/issues?q=is%3Aissue+is%3Aopen+sort%3Areactions-%2B1-desc). If others benefit from the changes in this proposal being added, please ask them to add :+1: to it.
