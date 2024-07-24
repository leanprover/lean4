#!/usr/bin/env bash

rm -rf .lake/build
lake exe "path with spaces"
touch .lake/build/bin/path
lake exe "path with spaces"
