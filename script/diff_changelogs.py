#!/usr/bin/env python3

import collections
import re
import sys

def parse(f):
    s = open(f, 'r').read()
    flgs = re.VERBOSE | re.MULTILINE
    [_, release, _] = re.split(r"""^\w.* \n   # master branch (aka work in progress)
                                    -+   \n+  # -------------""", s, maxsplit=2, flags=flgs)
    cats = re.split(r"^(?P<cat>\*.+\*)$  # *Features*", release, flags=flgs)
    cats = zip(cats[1::2], cats[2::2])
    return collections.OrderedDict([(cat[0], re.findall(r"^\*\ (?:.*(?:\n\ \ .*)*)  # * Implement ...", cat[1], flags=flgs)) for cat in cats])

def diff(oldf, newf):
    old = parse(oldf)
    new = parse(newf)
    for cat in new:
        items = [i for i in new[cat] if i not in old.get(cat,[])]
        if items:
            print(cat)
            print()
            print('\n\n'.join(items))
            print()

if __name__ == '__main__':
    diff(sys.argv[1], sys.argv[2])
