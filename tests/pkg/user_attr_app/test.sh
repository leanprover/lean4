#!/usr/bin/env bash

rm -rf .lake
lake build && ./.lake/build/bin/user_attr
