#!/usr/bin/env bash
set -euxo pipefail

./clean.sh

# Setup directory
mkdir -p inputs/barz/bam
echo foo > inputs/foo.txt
echo bar > inputs/barz/bar.txt
echo baz > inputs/barz/baz.txt
echo boo > inputs/barz/bam/boo.txt
echo untraced > inputs/untraced.txt
echo untraced > inputs/barz/untraced.txt
