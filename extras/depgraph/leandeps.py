#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright (c) 2015 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Authors: Soonho Kong, Leonardo de Moura, Ulrik Buchholtz

# Python 2/3 compatibility
from __future__ import print_function

import os
import sys
import getopt
import subprocess
import platform
import graphviz

g_lean_exec_name  = "lean"
if platform.system() == "Windows" or platform.system().startswith("MSYS"):
    g_lean_exec_name  = "lean.exe"

if platform.system().startswith("MSYS"):
    # In MSYS platform, realpath has a strange behavior.
    #    os.path.realpath("c:\a\b\c") => \:\a\b\c
    g_leanutil_path   = os.path.abspath(os.path.normpath(__file__))
else:
    g_leanutil_path   = os.path.abspath(os.path.realpath(__file__))

g_lean_bin_dir = os.path.dirname(g_leanutil_path)

g_lean_dir = os.path.dirname(g_lean_bin_dir)

g_lean_path = os.path.join(g_lean_bin_dir, g_lean_exec_name)

if not os.path.isfile(g_lean_path):
    error("cannot find lean executable at " + os.path.abspath(g_lean_path))

class lean_exception(Exception):
    def __init__(self, value):
        self.value = value
    def __str__(self):
        return repr(self.value)

def normalize_drive_name(name):
    if platform.system() == "Windows":
        drive, path = os.path.splitdrive(name)
        if drive == None:
            return name
        else:
            # Leo: return drive.lower() + path
            return path
    else:
        return name

def is_olean(fname):
    return fname.endswith(".olean")

def is_lean(fname):
    return fname.endswith(".lean")

def is_hlean(fname):
    return fname.endswith(".hlean")

LEAN_KIND=0
HLEAN_KIND=1
OLEAN_KIND=2

def get_lean_file_kind(fname):
    if is_lean(fname):
        return LEAN_KIND
    elif is_hlean(fname):
        return HLEAN_KIND
    elif is_olean(fname):
        return OLEAN_KIND
    else:
        raise lean_exception("unknown file kind: " + fname)

def olean_to_lean(fname, kind):
    if kind == LEAN_KIND:
        return fname[:-5] + "lean"
    elif kind == HLEAN_KIND:
        return fname[:-5] + "hlean"
    else:
        raise lean_exception("unsupported file kind: " + kind)

def lean_to_olean(fname):
    if is_lean(fname):
        return fname[:-4] + "olean"
    elif is_hlean(fname):
        return fname[:-5] + "olean"
    else:
        raise lean_exception("file '%s' is not a lean source file" % fname)

def get_timestamp(fname):
    try:
        return os.path.getmtime(fname)
    except OSError:
        return 0

def is_uptodate(fname):
    return get_timestamp(lean_to_olean(fname)) > get_timestamp(fname)

def lean_direct_deps(lean_file):
    deps = []
    proc = subprocess.Popen([g_lean_path, "--deps", lean_file],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = proc.communicate()[0].decode('utf-8').replace('\r\n', '\n')
    if not proc.returncode == 0:
        raise lean_exception(str(output))
    for olean_file in output.strip().splitlines():
        if olean_file:
            deps.append(normalize_drive_name(os.path.abspath(olean_file)))
    return deps

def get_lean_prefixes():
    paths = []
    proc = subprocess.Popen([g_lean_path, "--path"],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = proc.communicate()[0].decode('utf-8').replace('\r\n', '\n')
    if not proc.returncode == 0:
        raise lean_exception(str(output))
    for p in output.rstrip().split(':'):
        paths.append(os.path.normpath(os.path.abspath(p)))
    proc = subprocess.Popen([g_lean_path, "--hlean", "--path"],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = proc.communicate()[0].decode('utf-8').replace('\r\n', '\n')
    if not proc.returncode == 0:
        raise lean_exception(str(output))
    for p in output.rstrip().split(':'):
        paths.append(os.path.normpath(os.path.abspath(p)))
    return paths

def lean_to_module(fname, prefixes):
    root, ext = os.path.splitext(fname)
    for prefix in prefixes:
        if root.startswith(prefix):
            root = root[len(prefix)+1:]
            break
    return root.replace(os.sep, '.')

def lean_deps_core(lean_files, prefixes, visited, graph):
    for lean_file in lean_files:
        kind = get_lean_file_kind(lean_file)
        if not lean_file in visited:
            visited[lean_file] = True
            graph.node(lean_to_module(lean_file, prefixes))
            for d in lean_direct_deps(lean_file):
                d = os.path.normpath(os.path.abspath(str(d)))
                if is_olean(d):
                    d = olean_to_lean(d, kind)
                    graph.edge(lean_to_module(lean_file, prefixes), lean_to_module(d, prefixes))
                    lean_deps_core([d], prefixes, visited, graph)

def lean_deps(lean_files, prefixes, oname):
    visited = dict()
    graph   = graphviz.Digraph(name=oname,format='dot')
    lean_deps_core(lean_files, prefixes, visited, graph)
    graph.render()

def usage():
    print('Usage: '+sys.argv[0]+' [options] dir/file')
    print("\nIf argument is a directory, all source files below that directory")
    print("will be included in the graph.")
    print("\n  -h/--help : prints this message")
    print("  -o/--output file : saves the DOT output in the specified file")
    print("If no output file is specified, deps.gv and deps.gv.dot is written to.")

def main(argv):
    oname = "deps"
    try:
        opts, args = getopt.getopt(argv, "ho:", ["help","output="])
    except getopt.GetoptError as err:
        print(str(err))
        usage()
        sys.exit(2)
    for opt, arg in opts:
        if opt in ("-h", "--help"):
            usage()
            sys.exit()
        elif opt in ("-o", "--output"):
            oname = arg
    if len(args) != 1:
        print(" Input argument required!")
        usage()
        sys.exit(2)
    leanfiles = []
    prefixes = get_lean_prefixes()
    if os.path.isdir(args[0]):
        for root, dirs, files in os.walk(args[0]):
            for name in files:
                if is_lean(name) or is_hlean(name):
                    leanfiles.append(os.path.abspath(os.path.normpath(os.path.join(root, name))))
        prefixes.append(os.path.abspath(os.path.normpath(root)))
    elif is_lean(args[0]) or is_hlean(args[0]):
        leanfiles = [os.path.abspath(os.path.normpath(args[0]))]
    else:
        usage()
        sys.exit(2)
    lean_deps(leanfiles, prefixes, oname)

if __name__ == "__main__":
    main(sys.argv[1:])