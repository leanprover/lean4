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

rm *.txt -i || true
rm *.csv -i || true
rm -rf builds -I || true


COMMITS=("2024-03-31---15-55---tcg40" "2024-borrowing-benching-baseline" )
# COMMITS=(13a64ef64c3cd5c2066d66c1228ff789c06bc5d8 c016a25992392716885f5ba8fc5b3ddf7bec2467)
KINDS=("reuse" "noreuse")

for tag in "${COMMITS[@]}"; do
    git show --format="%H %ad" --date=short $tag -q
done

# Ask if script should proceed
read -p "Do you want to proceed? (y/n) " -n 1 -r
echo    # Move to a new line
if [[ $REPLY =~ ^[Yy]$ ]]; then
    echo "Proceeding to run..."
else
    echo "Run aborted."
    exit 1
fi


# REUSE_FILES=("$EXPERIMENTDIR/ResetReuse.baseline.lean.in" "$EXPERIMENTDIR/ResetReuse.research.lean.in")

for i in {0..1}; do
  echo "@@@ ${KINDS[i]} BUILD @@@"
  curl -d "Started[${KINDS[i]}]. run:$EXPERIMENTDIR. machine:$(uname -a)."  ntfy.sh/xISSztEV8EoOchM2
  mkdir -p $EXPERIMENTDIR/builds/
  git clone --depth 1 git@github.com:opencompl/lean4.git  --branch ${COMMITS[i]} $EXPERIMENTDIR/builds/${KINDS[i]}
  mkdir -p $EXPERIMENTDIR/builds/${KINDS[i]}/build/release/
  cd $EXPERIMENTDIR/builds/${KINDS[i]}/build/release/

  # output log name from stage3 build.
  CSVNAME="${KINDS[i]}.stage3.csv"
  PROFILE_FILE=$EXPERIMENTDIR/$CSVNAME

  cmake ../../ \
    -DCCACHE=OFF \
    -DRUNTIME_STATS=ON \
    -DCMAKE_BUILD_TYPE=Release \
    -DLEAN_RESEARCH_COMPILER_PROFILE_CSV_PATH=$PROFILE_FILE

  make -j10 stage2
  touch $EXPERIMENTDIR/$CSVNAME && echo "" > $EXPERIMENTDIR/$CSVNAME
  $TIME -v make -j10 stage3 2>&1 | tee "$EXPERIMENTDIR/time-${KINDS[i]}-stage3.txt"
  (cd $EXPERIMENTDIR/builds/${KINDS[i]}/build/release/stage3 && (ctest -E handleLocking -j32 --output-on-failure 2>&1 | tee "$EXPERIMENTDIR/ctest-${KINDS[i]}-stage3.txt")) || true
  curl -d "Done[${KINDS[i]}]. run:$EXPERIMENTDIR. machine:$(uname -a)."  ntfy.sh/xISSztEV8EoOchM2
done;
