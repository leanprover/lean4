#!/usr/bin/env bash
set -ex
find library -name '*.lean' -exec script/find_uppers.py {} \; | sort -u > script/uppers
> script/u
until [ $(cat script/u | wc -l) -eq $(cat script/uppers | wc -l) ]; do
    cat script/uppers > script/u
    cat script/u <(find library -name '*.lean' -exec script/chain_uppers.py {} \;) | sort -u > script/uppers
done
