#!/usr/bin/env bash
find library -name '*.lean' -exec script/camel.py {} \;
