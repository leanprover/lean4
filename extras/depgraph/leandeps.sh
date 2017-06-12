#!/usr/bin/env bash
set -e

sanitizer="s,\\.o\?lean,,g"
for dir in $(lean -p | tr : ' '); do
  if [[ -d $dir ]]; then
    dir=$(readlink -f $dir)
    sanitizer="$sanitizer;s,$dir/,,g"
  fi
done

echo 'digraph {'

for lean_fn in $(find $@ -name \*.lean -not -name .\*); do
  lean_fn=$(readlink -f $lean_fn)
  for dep_lean_fn in $(lean --deps $lean_fn); do
    echo "\"$lean_fn\" -> \"$dep_lean_fn\""
  done
done | sed "$sanitizer"

echo '}'
