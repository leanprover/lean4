#!/usr/bin/env bash
set -euxo pipefail

rm -rf .lake/build
(lake build 2>&1 && exit 1 || true) | grep --color -F 'does not exist'
