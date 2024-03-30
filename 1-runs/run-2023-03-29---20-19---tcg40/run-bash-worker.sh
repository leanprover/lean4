#!/usr/bin/env bash
set -o xtrace
set -e

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


rm -rf $ROOT/build || true
rm -rf $ROOT/build/noreuse || true
mkdir -p $ROOT/build/noreuse
cd $ROOT/build/noreuse

# == NO REUSE ==

echo "@@@ NOREUSE BUILD @@@"

CSVNAME=$(date +'%s---%d-%m-%Y---%H:%M:%S')
echo "CSV name is: $CSVNAME"
echo "output file is: OUTFOLDER/$CSVNAME"

KINDS=("noreuse" "reuse")
REUSE_ENABLED=(0 1)
REUSE_FILES=("$EXPERIMENTDIR/ResetReuse.baseline.lean.in" "$EXPERIMENTDIR/ResetReuse.research.lean.in")

for i in {0..1}; do
  BUILD_DIR="$ROOT/build/${KINDS[i]}"
  mkdir -p $BUILD_DIR
  cd $BUILD_DIR
  cp "${REUSE_FILES[i]}" "$ROOT/src/Lean/Compiler/IR/ResetReuse.lean"

  # output log name from stage3 build.
  CSVNAME="${KINDS[i]}.stage3.csv"

  PROFILE_FILE=$EXPERIMENTDIR/$CSVNAME
  cmake ../../ \
    -DCCACHE=OFF \
    -DRUNTIME_STATS=ON \
    -DLEAN_RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED=${REUSE_ENABLED[i]} \
    -DLEAN_RESEARCH_COMPILER_PROFILE_CSV_PATH=$PROFILE_FILE

  make -j10 stage2
  touch $EXPERIMENTDIR/$CSVNAME && echo "" > $EXPERIMENTDIR/$CSVNAME
  $TIME -v make -j10 stage3 2>&1 | tee "$EXPERIMENTDIR/time-${KINDS[i]}-stage3.txt"
  curl -d "Done[${KINDS[i]}]. run:$EXPERIMENTDIR. machine:$(uname -a)."  ntfy.sh/xISSztEV8EoOchM2
done;
