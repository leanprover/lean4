#!/usr/bin/env bash

rm -rf .lake/build
lake build 2>&1 | grep 'error: field.*private'
