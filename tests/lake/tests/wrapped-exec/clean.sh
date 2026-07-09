#!/usr/bin/env bash
# Removes build state only. The test compares sums captured BETWEEN clean
# invocations, so we deliberately don't touch them here.
rm -rf .lake lake-manifest.json produced.out
