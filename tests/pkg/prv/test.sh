#!/usr/bin/env bash

rm -rf .lake
lake build 2>&1 | grep 'error: .*: field.*private'
