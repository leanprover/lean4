---
name: ci-log-retrieval
description: Retrieve and investigate failing Lean CI job logs. Use when a CI job fails and you need to fetch its logs, or when monitoring a CI run for failures.
allowed-tools: Bash
---

# CI Log Retrieval

When CI jobs fail, investigate immediately — don't wait for other jobs to complete. Individual job
logs are often available even while other jobs are still running.

Try:

```bash
gh run view <run-id> --log
gh run view <run-id> --log-failed
gh run view <run-id> --job=<job-id>   # target the specific failed job
```

Sleeping is fine when asked to monitor CI and no failures exist yet, but once any job fails,
investigate that failure immediately.
