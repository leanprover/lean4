#!/usr/bin/env bash
set -euxo pipefail

./clean.sh

# Setup directory
mkdir -p inputs/barz
echo foo > inputs/foo.txt
echo bar > inputs/barz/bar.txt
echo baz > inputs/barz/baz.txt
echo untraced > inputs/untraced.txt
echo untraced > inputs/barz/untraced.txt
