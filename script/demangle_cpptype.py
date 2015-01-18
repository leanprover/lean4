#!/usr/bin/env python
#
# Copyright (c) 2013 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Author: Soonho Kong
#
# What's this?
# ============
# It takes an input from stdin and demangle c++ type if the line
# matches the following patten:
#
#     .* : <C++_TYPE> := .*
#
# which, is the format that we are using in lean_assert.
#
# It calls "c++filt" to do the work.
#

# Python 2/3 compatibility
from __future__ import print_function

import re
import sys
import subprocess
import fileinput

pattern_str = "(.* : )([A-Za-z0-9]+)( := .*)"
pattern = re.compile(pattern_str)
cppfilt = "c++filt"
cppfilt_option = "--types"

def process_line(line):
    result = pattern.match(line);
    if result == None:
        print(line, end=' ')
    else:
        p = subprocess.Popen(cppfilt + " " + cppfilt_option + " " + result.group(2),
                             shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        ty = p.stdout.readlines()[0].strip()
        retval= p.wait()
        new_str = re.sub(pattern_str, r"\1" + ty + r"\3", line);
        print(new_str, end=' ')

if len(sys.argv) > 1:
    for line in fileinput.input():
        process_line(line)
else:
    while True:
        line = sys.stdin.readline()
        if not line:
            break
        process_line(line)
