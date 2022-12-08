#!/usr/bin/env bash

rm -rf build
lake build && ./build/bin/user_attr
