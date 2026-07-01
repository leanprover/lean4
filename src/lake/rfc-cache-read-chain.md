### Proposal

`lake cache get` resolves against one storage service per invocation. This RFC adds a configurable ordered read chain, so a single `lake cache get` resolves mappings and artifacts across multiple endpoints, routing each output to the service that hosts it.

The chain is a content-addressed multi-source resolver. Because artifacts are verified by hash, any service's copy of a hash is interchangeable.

#### Proposed configuration

`cache.getChain` is a new, priority-ordered list of service names in Lake's cache config (system or job-provided), resolved against the existing `cache.service` definitions; the loader maps each name to a `CacheService`. `kind` is unchanged. (The per-service `scope` and `revDiscovery` fields are specified by the companion `revDiscovery` RFC.)

```toml
[cache]
getChain = ["master", "forks"]   # ordered, highest-trust first

[[cache.service]]
name = "master"
kind = "s3"
artifactEndpoint = "https://…/master/artifacts"
revisionEndpoint = "https://…/master/revisions"

[[cache.service]]
name = "forks"
kind = "s3"
artifactEndpoint = "https://…/forks/artifacts"
revisionEndpoint = "https://…/forks/revisions"
```


#### Proposed lookup algorithm

With a configured `getChain`, `lake cache get`:

1. Resolves config and the package's scope, platform, and toolchain (as today).
2. Resolves a revision per service.
3. Fetches each service's mapping for that revision and unions them over input hashes; on a collision the earliest service wins and is that entry's mapping origin.
4. Fetches each output's artifacts from its origin.
5. Writes each input's local outputs file: its output data and its origin as provenance.

`--mappings-only` stops after step 3; provenance is still the origin, and a later build lazy-fetches each artifact from it.

#### Provenance

An output's provenance is a single service, its origin ([`Cache.lean:341-360`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/Config/Cache.lean#L341-L360)). The remote map is unchanged, still `[inputHash, output]` ([`Cache.lean:30-33`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/Config/Cache.lean#L30-L33)), so provenance lives only in the local cache. Because `put` uploads an artifact before the mapping that lists it ([`Main.lean:639-641`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/CLI/Main.lean#L639-L641)), a service whose mapping names an output holds the artifact, so a build fetches it from the recorded origin in one request. Any service with the hash serves identical bytes, so a get may read an output from a nearer one; the recorded origin is unchanged.

#### Benefits

- Locality/latency: `[local-disk, team-mirror, org-bucket, public]`, first-hit, for speed and bandwidth.
- Provenance: a project can combine its own cache plus each dependency's published cache, routed per hash. A project's artifacts resolve from its own cache; a dependency's misses fall through to that dependency's source. Generalizes today's per-package Reservoir handling to arbitrary backends.
- Backend migration: a `[new, legacy]` chain drains a legacy backend while writes move to the new one, with no flag day.
- Trust: trust-segregated services (e.g., the separate Azure containers the mathlib cache tool uses).
- Redundancy strategies: e.g., primary cache plus mirror services for outages and rate limits; geo-local or free-egress services.

#### Working 'manual' alternative: external orchestration

This 'read chain' can be achieved like this today with `lake`:

1. `lake cache get --service master` to populate the local pool.
2. `lake cache get --service forks --scope <derived-scope>`, using skip-if-already-local to fetch only deltas.

Note this requires computing `--scope` / merge-base externally.

This is a tad fragile: a single `cache get` binds one manifest to one `(service, scope)`, so a missing artifact fails the whole get.

#### Security

This RFC changes only the read path: `cache put` and the write-side boundary (which endpoint a job may write to, enforced by CI credentials and storage access policies) are unchanged. Reading artifacts from an untrusted service is safe by content-addressing; the trust model for mapping sources is the companion `revDiscovery` RFC's concern.

#### Alternatives considered

- `lake exe cache` orchestrator (Mathlib's current pattern): a shipped executable that drives `lake cache` to coalesce endpoints. But a get binds one manifest to one `(service, scope)`, so an exe cannot produce a single manifest that routes each output to its origin. It complements the chain as a policy layer; it does not replace it.
- Multiple recorded sources per artifact: rejected. The origin's mapping lists the output, so it holds the artifact and one recorded source per output is enough.
- Self-contained endpoints: keep the full artifact set in each endpoint, so no chain is needed. Works, but forfeits the storage savings and the other benefits above.

#### Open questions

- Per-dependency sources: associating each dependency with its own cache, beyond a single global `getChain`, may want per-package configuration.

#### Backwards compatibility

Additive. Without `cache.getChain`, `cache get` is unchanged. Chain is opt-in; existing flags and env vars unaffected.

#### User Experience

One `lake cache get` coalesces artifacts across all configured sources, replacing the per-service invocations and manual orchestration above: no per-service sequencing, no caller-computed flags, and per-output routing the manual approach cannot provide.

#### Beneficiaries

Downstream projects that want their dependencies' caches and their own in one command; teams putting a local or LAN mirror in front of a public cache; projects migrating cache backends; and trust-segregated setups (also see the companion `revDiscovery` RFC: #14151).

Mathlib's migration of its multi-container cache (leanprover-community/mathlib4#40035) is the immediate example of trust segregation without duplicate storage costs.

#### Maintainability

Additive, reuses existing machinery: mapping merge unions maps `cache get` already loads, artifact fetches reuse the transfer engine ([`Cache.lean:756-878`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/Config/Cache.lean#L756-L878)), provenance fills an existing per-output field. No new transport, storage, on-the-wire format, or change to the single-service path.

### Impact

Add :+1: to [issues you consider important](https://github.com/leanprover/lean4/issues?q=is%3Aissue+is%3Aopen+sort%3Areactions-%2B1-desc). If others benefit from the changes in this proposal being added, please ask them to add :+1: to it.
