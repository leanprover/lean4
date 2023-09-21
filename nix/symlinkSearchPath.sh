#!/usr/bin/env bash

# Given a target directory and one (or more) `lean-deps.txt` file, as built by buildLeanPackage,
# recursively traverses it and symlinks the contents into one big directory.

set -e

# first argument: directory to create
dest="$1"
shift

# remaining arguments: lean-dep.txt files
# read their lines into the todo array
declare -a todo
for file in "$@"
do
    readarray -t -O ${#todo[@]} todo < "$file"
done

mkdir "$dest"

# simple work-list algorithm
declare -A seen
while [ ${#todo[@]} -gt 0 ]
do
  n=$((${#todo[@]}-1))
  dir="${todo[n]}"
  unset "todo[$n]"
  if ! [[ -v "seen[$dir]" ]]
  then
    seen[$dir]="seen"
    cp -rs --no-preserve=mode "$dir"/. "$dest"
    rm "$dest"/lean-deps.txt
    readarray -t -O ${#todo[@]} todo < "$dir"/lean-deps.txt
  fi
done
