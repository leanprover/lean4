### Proposal

A custom S3 cache service can only be used by passing `--scope`/`--repo` on every `cache get` ([`Main.lean:565-566`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/CLI/Main.lean#L565-L566)), and `CacheServiceConfig` has no `scope` field ([`LakeConfig.lean:30-42`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/Config/LakeConfig.lean#L30-L42)). This RFC adds `scope` as a per-service config field — omitted or `""` means a flat content-addressed layout, a string is a fixed path prefix — with `--scope`/`--repo` kept as per-call overrides. A bare `lake cache get --service <name>` then works without a scope flag.

#### Background

Scope is the path prefix under which a service stores artifacts (`{endpoint}/{scope}/{hash}.art`) and mappings (`{endpoint}/{scope}/{rev}.jsonl`). Today it comes only from the CLI for S3 services, or is derived from package fields for Reservoir (`reservoirScope`). A flat content-addressed bucket has no meaningful scope, yet the CLI still demands one.

#### Current state

For a custom (non-Reservoir) service, `cache get` requires `--scope` or `--repo`; with neither it errors ([`Main.lean:565-566`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/CLI/Main.lean#L565-L566)). The service config carries endpoints and `kind`, but no scope ([`LakeConfig.lean:30-42`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/Config/LakeConfig.lean#L30-L42)).

#### The change

Add `scope` to `CacheServiceConfig`:

- omitted / `""` → flat layout (`{endpoint}/{hash}.art`, `{endpoint}/{rev}.jsonl`).
- a string → fixed prefix.

`--scope`/`--repo` override per call. Drop the requirement that a custom-service get carry a scope.

#### Configuration sketch

```toml
[[cache.service]]
name = "mycache"
kind = "s3"
artifactEndpoint = "https://…/artifacts"
revisionEndpoint = "https://…/revisions"
scope = ""                       # flat; or a fixed prefix like "myproject"
```

`lake cache get --service mycache` then needs no scope flag.

#### Security

Scope is the operator describing where to read, which is already their responsibility; reads remain hash-verified ([`Cache.lean:778-783`](https://github.com/leanprover/lean4/blob/cb5e33763601d9460805607bfb7ffc5fc69119d7/src/lake/Lake/Config/Cache.lean#L778-L783)), so the layout choice carries no trust weight. Read isolation does not depend on scope (see the SHA-isolation RFC).

#### Alternatives considered

- CLI-only scope (status quo): forces `--scope` on every call and blocks flat buckets that have no meaningful scope.
- A special "absent `--scope` means flat" CLI rule: works, but a per-service config field is explicit, persists, and expresses fixed prefixes too.

#### Open questions

- Precedence of a config `scope` vs a per-call `--scope`/`--repo` (override, or error on conflict).
- How an explicit `scope` interacts with Reservoir, whose scope is derived from package fields.

#### Backwards compatibility

Flows that pass `--scope`/`--repo` are unaffected. The change removes the error for the no-scope case, so a service with no configured scope and no flag becomes flat instead of failing.

#### User Experience

A service's layout is set once in config; `lake cache get --service <name>` works with no scope flag. Both flat and prefixed layouts are expressible per service.

#### Beneficiaries

Anyone running an S3-backed Lake cache who would rather configure the layout once than pass `--scope` on every call, and flat content-addressed buckets that have no scope to pass. Also an enabler for a bare, flagless `lake cache get` in the SHA-isolation and read-chain RFCs.

#### Maintainability

Small: one config field plus relaxing one CLI check. No new transport or storage.

### Community Feedback

Not yet discussed on Zulip. I will open a thread on #lake and summarize and link it here.

### Impact

Add :+1: to [issues you consider important](https://github.com/leanprover/lean4/issues?q=is%3Aissue+is%3Aopen+sort%3Areactions-%2B1-desc). If others benefit from the changes in this proposal being added, please ask them to add :+1: to it.
