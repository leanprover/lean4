#!/bin/sh
Hash=`git rev-parse HEAD`
cat > $1/githash.h <<EOF
// Automatically generated file, DO NOT EDIT
char const * g_githash = "$Hash";
EOF
