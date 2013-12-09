#!/bin/bash
# Auxiliary script that succeeds iff if the execution of input
# arguments fail.
if $*; then
   echo "unexpected success"
   exit 1
fi
