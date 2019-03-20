#!/usr/bin/env bash
find library -name '*.lean' -exec script/camel.py {} \;
script/camel.py src/library/constants.txt
