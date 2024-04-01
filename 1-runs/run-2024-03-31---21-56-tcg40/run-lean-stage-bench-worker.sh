#!/usr/bin/env bash
set -o xtrace
set -e

COMMIT_TO_BENCH="2024-03-31---19-38---tcg40"

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


COMMITS=("$COMMIT_TO_BENCH" "2024-borrowing-benching-baseline" )
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

mkdir -p $EXPERIMENTDIR/builds/

git clone --depth 1 git@github.com:opencompl/lean4.git --branch 2024-borrowing-benching-baseline $EXPERIMENTDIR/builds/baseline-src-code

for i in {0..1}; do
  echo "@@@ ${KINDS[i]} BUILD @@@"
  curl -d "Started[${KINDS[i]}]. run:$EXPERIMENTDIR. machine:$(uname -a)."  ntfy.sh/xISSztEV8EoOchM2
  mkdir -p $EXPERIMENTDIR/builds/
  git clone --depth 1 git@github.com:opencompl/lean4.git  --branch ${COMMITS[i]} $EXPERIMENTDIR/builds/${KINDS[i]} --reference /anfs/bigdisc/sb2743/24-borrowing/lean4.reference
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
  make update-stage0
  rm -rf ../../src/; cp -r $EXPERIMENTDIR/builds/baseline-src-code/src ../../
  git checkout -- ../../src/runtime ../../src/include/lean/lean.h ../../src/library/compiler/ir_interpreter.h

  make -j10 stage2
  rm $EXPERIMENTDIR/$CSVNAME || true
  $TIME -v make -j10 stage3 2>&1 | tee "$EXPERIMENTDIR/time-${KINDS[i]}-stage3.txt"
  cp "$EXPERIMENTDIR/$CSVNAME" "$EXPERIMENTDIR/${KINDS[i]}.stage3-compile.csv"
  (cd $EXPERIMENTDIR/builds/${KINDS[i]}/build/release/stage3 && (ctest -E handleLocking -j32 --output-on-failure 2>&1 | tee "$EXPERIMENTDIR/ctest-${KINDS[i]}-stage3.txt")) || true
  curl -d "Done[${KINDS[i]}]. run:$EXPERIMENTDIR. machine:$(uname -a)."  ntfy.sh/xISSztEV8EoOchM2
done;
