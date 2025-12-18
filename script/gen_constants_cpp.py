#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright (c) 2015 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Author: Leonardo de Moura
#
# Given a text file containing constants defined in the Lean libraries,
# this script generates .h and .cpp files for initialing/finalizing these constants
# as C++ name objects.
#
# This script is used to generate src/library/constants.cpp and src/library/constants.h
import sys
import os
import re

def error(msg):
    print("Error: %s" % msg)
    exit(1)

def to_c_const(s):
    # insert '_' instead of '.', between lower case and upper case, and after 'IO'
    s = re.sub(r"\.|(?<=[a-z0-9])(?=[A-Z])|(?<=IO)(?=[A-Z][a-z])", '_', s)
    return s.lower()

def main(argv=None):
    if argv is None:
        argv = sys.argv[1:]
    infile        = argv[0]
    constants     = []
    with open(infile, 'r') as f:
        for line in f:
            p = line.split()
            if len(p) == 2:
                constants.append([p[1].strip(), p[0].strip()])
            else:
                constants.append([to_c_const(line.strip()), line.strip()])

    basedir, name = os.path.split(infile)
    os.chdir(basedir)
    basename, ext = os.path.splitext(name)
    cppfile       = basename + ".cpp"
    hfile         = basename + ".h"
    tst_file      = "../../tests/lean/run/check_" + basename + ".lean"
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
            f.write('    mark_persistent(g_%s->raw());\n' % c[0])
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
    for c in constants:
        cmd = ("cd .. && grep --silent --include=\"*.h\" --include=\"*.cpp\" --exclude=\".#*\" --exclude=\"constants.*\" -R \"get_%s_name\" *" % c[0])
        if os.system(cmd) != 0:
            print("Warning: generated function 'get_%s_name' is not used in the source code" % c[0])
    # TODO: enable test file again
    return 0
    with open(tst_file, 'w') as f:
        f.write('-- DO NOT EDIT, automatically generated file, generator scripts/gen_constants_cpp.py\n')
        f.write("import init.io\n")
        f.write("open tactic\n");
        f.write("meta def script_check_id (n : name) : tactic unit :=\n");
        f.write("do env ← get_env, (env^.get n >> return ()) <|> (guard $ env^.is_namespace n) <|> (attribute.get_instances n >> return ()) <|> fail (\"identifier '\" ++ to_string n ++ \"' is not a constant, namespace nor attribute\")\n");
        for c in constants:
            f.write("run_cmd script_check_id `%s\n" % c[1])
    print("done")
    return 0

if __name__ == "__main__":
    sys.exit(main())
