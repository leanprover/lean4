#!/usr/bin/env bash
set -euo pipefail

# Test that Lean will use the specified olean from `header.json`
lean Dep.lean -o Dep.olean
lean Test.lean --header header.json
