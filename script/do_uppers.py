#!/usr/bin/env python3
import regex as re
import os
import sys

# https://stackoverflow.com/a/19053800
def to_camel_case(snake_str):
    components = snake_str.split('_')
    # We capitalize the first letter of each component except the first one
    # with the 'title' method and join them together.
    return components[0] + ''.join(x.title() for x in components[1:])

uppers = set(s.strip() for s in open('script/uppers').readlines())
candidate = re.compile(r"(?!type class|monad transformer)\w+", re.MULTILINE)
fpath = sys.argv[1]
with open(fpath) as f:
    s = f.read()
s = candidate.sub(lambda w: w[0][0].upper() + w[0][1:] if w[0] in uppers else w[0], s)
with open(fpath, "w") as f:
    f.write(s)
