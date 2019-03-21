#!/usr/bin/env bash
find library -name '*.lean' -exec script/do_uppers.py {} \;
find tests -name '*.lean' -exec script/do_uppers.py {} \;
script/do_uppers.py src/library/constants.txt
