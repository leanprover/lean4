#!/bin/bash
# Auxiliary script for redirecting input
#   Given the arguments $1 ... $n-1 $n,
#   it executes the command
#        $1 ... $n-1 < $n
# This is a hack to workaround a ctest limitation
length=$(($#-1))
array=${@:1:$length}
shift `expr $# - 1`
last=`echo $1`
$array < $last
