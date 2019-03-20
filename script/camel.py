#!/usr/bin/env python3
import re
import os
import sys

# https://stackoverflow.com/a/19053800
def to_camel_case(snake_str):
    components = snake_str.split('_')
    # We capitalize the first letter of each component except the first one
    # with the 'title' method and join them together.
    return components[0] + ''.join(x.title() for x in components[1:])

snake = re.compile("[^\W_]+_\w+", re.MULTILINE)
fpath = sys.argv[1]
with open(fpath) as f:
    s = f.read()
s = snake.sub(lambda m: to_camel_case(m[0]), s)
with open(fpath, "w") as f:
    f.write(s)
