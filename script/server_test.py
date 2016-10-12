#!/usr/bin/env python3
#
# Copyright (c) 2016 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Author: Gabriel Ebner
#

import sys, subprocess, json, time

_, file_name = sys.argv

proc = subprocess.Popen(["lean", "--server"],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        universal_newlines=True, bufsize=1)

def send(req):
    proc.stdin.write(json.dumps(req) + "\n")
    print(proc.stdout.readline().rstrip())

while True:
    content = open(file_name).read()
    send({ 'command': 'sync', 'file_name': file_name, 'content': content })
    send({ 'command': 'check' })
    time.sleep(1)
