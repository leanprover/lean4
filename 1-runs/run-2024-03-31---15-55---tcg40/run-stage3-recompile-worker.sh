#!/usr/bin/env bash
set -o xtrace
set -e

# --------

EXPERIMENTDIR=$(pwd)
echo "pwd: $EXPERIMENTDIR"
DATE=$(date)
echo "date: $DATE"
MACHINE=$(uname -a)
echo "machine: $MACHINE"
echo "git status: $(git status --short)"
echo "git commit: $(git rev-parse HEAD)"
ROOT=$(git rev-parse --show-toplevel)
echo "root folder: $ROOT"
echo "out folder: $OUTFOLDER"

if [ "$(uname -s)" = "Darwin" ]; then
    TIME="gtime"
else
    TIME="command time"
fi
echo "time: $TIME"
$TIME -v echo "time"

KINDS=("reuse" "noreuse")

for i in {0..1}; do
  curl -d "Start[stage3-recompile-${KINDS[i]}]. run:$EXPERIMENTDIR. machine:$(uname -a)."  ntfy.sh/xISSztEV8EoOchM2
  rm -rf $EXPERIMENTDIR/builds/${KINDS[i]}/build/release/
  mkdir -p $EXPERIMENTDIR/builds/${KINDS[i]}/build/release/
  cd $EXPERIMENTDIR/builds/${KINDS[i]}/build/release/
  make -j10 stage2
  CSVNAME="${KINDS[i]}.stage3.csv"
  rm $EXPERIMENTDIR/$CSVNAME # cleanup old csv.
  $TIME -v make -j10 stage3 2>&1 | tee $EXPERIMENTDIR/time-rebuild-stdlib-stage3-${KINDS[i]}.txt # make new CSV.
  curl -d "Done[stage3-recompile-${KINDS[i]}]. run:$EXPERIMENTDIR. machine:$(uname -a)."  ntfy.sh/xISSztEV8EoOchM2
done;
