#!/usr/bin/env bash

rm -rf .lake
lake build -v 2>&1 | grep 'hello, test, world'
