#!/usr/bin/env python

import argparse
import collections
import os
import sys
import urllib.error
import urllib.request
try:
    import mistune
except ImportError:
    print("Mistune package not found. Install e.g. via `pip install mistune`.")

parser = argparse.ArgumentParser(description="Check all *.md files of the current directory's subtree for broken links.")
parser.add_argument('--http', help="also check external links (can be slow)", action='store_true')
parser.add_argument('--check-missing', help="also find unreferenced lean files", action='store_true')
args = parser.parse_args()

lean_root = os.path.join(os.path.dirname(__file__), os.path.pardir)
lean_root = os.path.normpath(lean_root)
result = {}

def check_link(link, root):
    if link.startswith('http'):
        if not args.http:
            return True
        if link not in result:
            try:
                urllib.request.urlopen(link)
                result[link] = True
            except:
                result[link] = False
        return result[link]
    else:
        if link.startswith('/'):
            # project root-relative link
            path = lean_root + link
        else:
            path = os.path.join(root, link)

        path = os.path.normpath(path) # should make it work on Windows

        result[path] = os.path.exists(path)
        return result[path]

# check all .md files
for root, _, files in os.walk('.'):
    for f in files:
        if not f.endswith('.md'):
            continue

        path = os.path.join(root, f)

        class CheckLinks(mistune.Renderer):
            def link(self, link, title, content):
                if not check_link(link, root):
                    print("Broken link", link, "in file", path)

        mistune.Markdown(renderer=CheckLinks())(open(path).read())

if args.check_missing:
    # check all .(h)lean files
    for root, _, files in os.walk('.'):
        for f in files:
            path = os.path.normpath(os.path.join(root, f))
            if (path.endswith('.lean') or path.endswith('.hlean')) and path not in result:
                result[path] = False
                print("Missing file", path)

if not all(result.values()):
    sys.exit(1)
