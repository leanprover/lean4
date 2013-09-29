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
import re
import subprocess
import fileinput

pattern_str = "(.* : )([A-Za-z0-9]+)( := .*)"
pattern = re.compile(pattern_str)
cppfilt = "c++filt"
cppfilt_option = "--types"

for line in fileinput.input():
    result = pattern.match(line);
    if result == None:
        print line,
    else:
        p = subprocess.Popen(cppfilt + " " + cppfilt_option + " " + result.group(2),
                             shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        ty = p.stdout.readlines()[0].strip()
        retval= p.wait()
        new_str = re.sub(pattern_str, r"\1" + ty + r"\3", line);
        print new_str,
