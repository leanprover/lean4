#!/usr/bin/env bash

rm -rf .lake/build
lake build && ./.lake/build/bin/user_attr
