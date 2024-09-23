#!/bin/bash
# Must be run in a copy of the `lean4` repository, and you'll need to login with `gh auth` first.
for v in $(gh release list | cut -f1) nightly stable
do
  sleep 15 # Don't exceed API rate limits!
  echo -n $v" "
  count=$(gh search code --filename lean-toolchain -L 1000 "leanprover/lean4:$v" | wc -l)
  
  # Check if version number begins with a 'v'
  if [[ $v == v* ]]; then
    sleep 5 # Don't exceed API rate limits!
    # Remove the leading 'v'
    v_no_v=${v:1}
    count_no_v=$(gh search code --filename lean-toolchain -L 1000 "leanprover/lean4:$v_no_v" | wc -l)
    # Sum the two counts
    total_count=$(($count + $count_no_v))
    echo $total_count
  else
    echo $count
  fi
done | awk '{ printf "%-12s %s\n", $1, $2 }'
