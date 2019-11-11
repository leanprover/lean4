#!/bin/bash
LEAN=$1
FILE=$2
export LEAN_PATH=.:../../library/standard
$LEAN $2
