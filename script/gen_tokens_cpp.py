#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright (c) 2015 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Author: Leonardo de Moura
#
# Given a text file containing id and token strings,
# this script generates .h and .cpp files for initialing/finalizing these tokens
# as C++ name objects.
#
# This script is used to generate src/frontends/lean/tokens.cpp and src/frontends/lean/tokens.h
# from src/frontends/lean/tokens.txt
import sys
import os

def error(msg):
    print("Error: %s" % msg)
    exit(1)

def to_c_const(s):
    out = ""
    for c in s:
        if c == '.' or c == '_':
            out += '_'
        elif c.isalpha() or c.isdigit():
            out += c
        else:
            error("unsupported character in constant: %s" % s)
    return out

def main(argv=None):
    if argv is None:
        argv = sys.argv[1:]
    infile        = argv[0]
    basename, ext = os.path.splitext(infile)
    cppfile       = basename + ".cpp"
    hfile         = basename + ".h"
    constants     = []
    with open(infile, 'r') as f:
        for line in f:
            l = line.split()
            if len(l) != 2:
                error("invalid line: %s" % line)
            constants.append([to_c_const(l[0].strip()), l[1].strip()])
    with open(hfile, 'w') as f:
        f.write('// Copyright (c) 2015 Microsoft Corporation. All rights reserved.\n')
        f.write('// Released under Apache 2.0 license as described in the file LICENSE.\n')
        f.write('// DO NOT EDIT, automatically generated file, generator scripts/get_tokens_cpp.py\n')
        f.write('#include "util/name.h"\n')
        f.write('namespace lean {\n')
        f.write('void initialize_tokens();\n')
        f.write('void finalize_tokens();\n')
        for c in constants:
            f.write('name const & get_%s_tk();\n' % c[0])
        f.write('}\n')
    with open(cppfile, 'w') as f:
        f.write('// Copyright (c) 2015 Microsoft Corporation. All rights reserved.\n')
        f.write('// Released under Apache 2.0 license as described in the file LICENSE.\n')
        f.write('// DO NOT EDIT, automatically generated file, generator scripts/gen_tokens_cpp.py\n')
        f.write('#include "util/name.h"\n')
        f.write('namespace lean{\n')
        # declare constants
        for c in constants:
            f.write('static name const * g_%s_tk = nullptr;\n' % c[0])
        # initialize constants
        f.write('void initialize_tokens() {\n')
        for c in constants:
            f.write('    g_%s_tk = new name{' % c[0])
            f.write('"%s"' % c[1])
            f.write('};\n')
        f.write('}\n')
        # finalize constants
        f.write('void finalize_tokens() {\n')
        for c in constants:
            f.write('    delete g_%s_tk;\n' % c[0])
        f.write('}\n')
        # get methods
        for c in constants:
            f.write('name const & get_%s_tk() { return *g_%s_tk; }\n' % (c[0], c[0]))
        # end namespace
        f.write('}\n')
    print("done")
    return 0

if __name__ == "__main__":
    sys.exit(main())
