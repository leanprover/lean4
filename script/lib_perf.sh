#!/bin/bash
# Script for collecting compilation times for the standard library
# It assumes the lean binary is at the bin directory
# It assumes the programs time and realpath are available
set -eu
TIME=/usr/bin/time
REALPATH=realpath

if ! command -v $TIME 2> /dev/null > /dev/null; then
    TIME=gtime
fi

MY_PATH="`dirname \"$0\"`"
LEAN=$MY_PATH/../bin/lean
LIB=$MY_PATH/../library
for f in `find $LIB -name '*.lean'`; do
  rf=`$REALPATH $f`
  $TIME --format="$rf %e" $LEAN -j 0 $rf > /dev/null
done
