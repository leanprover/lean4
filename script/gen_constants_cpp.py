#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright (c) 2015 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Author: Leonardo de Moura
#
# Given a text file containing constants defined in the Lean libraries,
# this script generates .h and .cpp files for initialing/finalizing theses constants
# as C++ name objects.
#
# This script is used to generate src/library/constants.cpp and src/library/constants.h
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
            constants.append([to_c_const(line.strip()), line.strip()])
    with open(hfile, 'w') as f:
        f.write('// Copyright (c) 2015 Microsoft Corporation. All rights reserved.\n')
        f.write('// Released under Apache 2.0 license as described in the file LICENSE.\n')
        f.write('// DO NOT EDIT, automatically generated file, generator scripts/gen_constants_cpp.py\n')
        f.write('#include "util/name.h"\n')
        f.write('namespace lean {\n')
        f.write('void initialize_constants();\n')
        f.write('void finalize_constants();\n')
        for c in constants:
            f.write('name const & get_%s_name();\n' % c[0])
        f.write('}\n')
    with open(cppfile, 'w') as f:
        f.write('// Copyright (c) 2015 Microsoft Corporation. All rights reserved.\n')
        f.write('// Released under Apache 2.0 license as described in the file LICENSE.\n')
        f.write('// DO NOT EDIT, automatically generated file, generator scripts/gen_constants_cpp.py\n')
        f.write('#include "util/name.h"\n')
        f.write('namespace lean{\n')
        # declare constants
        for c in constants:
            f.write('name const * g_%s = nullptr;\n' % c[0])
        # initialize constants
        f.write('void initialize_constants() {\n')
        for c in constants:
            f.write('    g_%s = new name{' % c[0])
            first = True
            for part in c[1].split('.'):
                if not first:
                    f.write(", ")
                f.write('"%s"' % part)
                first = False
            f.write('};\n')
        f.write('}\n')
        # finalize constants
        f.write('void finalize_constants() {\n')
        for c in constants:
            f.write('    delete g_%s;\n' % c[0])
        f.write('}\n')
        # get methods
        for c in constants:
            f.write('name const & get_%s_name() { return *g_%s; }\n' % (c[0], c[0]))
        # end namespace
        f.write('}\n')
    print("done")
    return 0

if __name__ == "__main__":
    sys.exit(main())
