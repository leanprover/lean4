#!/usr/bin/env bash
set -o xtrace
set -e

echo "pwd: $(pwd)"
DATE=$(date)
echo "date: $DATE"
MACHINE=$(uname -a)
echo "machine: $MACHINE"
echo "git status: $(git status --short)"
echo "git commit: $(git rev-parse HEAD)"
ROOT=$(git rev-parse --show-toplevel)
echo "root folder: $ROOT"
OUTFOLDER=$(pwd)
echo "out folder: $OUTFOLDER"

if [ "$(uname -s)" = "Darwin" ]; then
    TIME="gtime"
else
    TIME="command time"
fi
echo "time: $TIME"
$TIME -v echo "time"


rm -rf $ROOT/build || true
mkdir -p $ROOT/build/incorrect
cd $ROOT/build/incorrect

# == NO REUSE ==

echo "@@@ NOREUSE BUILD @@@"

CSVNAME=$(date +'%s---%d-%m-%Y---%H:%M:%S')
echo "CSV name is: $CSVNAME"
echo "output file is: OUTFOLDER/$CSVNAME"

cp ResetReuse.baseline.lean.in ../../src/Lean/Compiler/IR/ResetReuse.lean
cmake ../../ \
  -DCCACHE=OFF \
  -DRUNTIME_STATS=OFF \
  -DLEAN_RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED=0 \
  -DLEAN_RESEARCH_COMPILER_PROFILE_CSV_PATH=$OUTFOLDER/$CSVNAME

make -j stage1
make -j stage2
touch ../../src/Init/Prelude.lean
touch $OUTFOLDER/$CSVNAME && echo "" > $OUTFOLDER/$CSVNAME
$TIME -v make -j stage2 2>&1 | tee "time-noreuse-stage2.txt"
mv $OUTFOLDER/$CSVNAME $OUTFOLDER/$CSVNAME.noreuse.stage2.csv
# $TIME -v make -j stage3 &> "time-noreuse-stage3.txt"
# mv $OUTFOLDER/$CSVNAME $OUTFOLDER/$CSVNAME.noreuse.stage3.csv

curl -d "Done[noreuse]\n*machine:$(uname -a)\n*folder:$OUTFOLDER\n*machine:$MACHINE" ntfy.sh/xISSztEV8EoOchM2
# == REUSE ==

echo "@@@ REUSE BUILD @@@"

CSVNAME="$(date +'%s---%d-%m-%Y---%H:%M:%S')"
echo "output file is: $OUTFOLDER/$CSVNAME"

cp ResetReuse.research.lean.in ../../src/Lean/Compiler/IR/ResetReuse.lean

cmake ../../ \
  -DCCACHE=OFF \
  -DRUNTIME_STATS=OFF \
  -DLEAN_RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED=1 \
  -DLEAN_RESEARCH_COMPILER_PROFILE_CSV_PATH=$OUTFOLDER/$CSVNAME
make -j stage1
make -j stage2
touch ../../src/Init/Prelude.lean
touch $OUTFOLDER/$CSVNAME && echo "" > $OUTFOLDER/$CSVNAME
$TIME -v make -j stage2 2>&1 | tee "time-reuse-stage2.txt"
mv $OUTFOLDER/$CSVNAME $OUTFOLDER/$CSVNAME.reuse.stage2.csv

echo "DONE!"
curl -d "Done fully\n*machine:$(uname -a)\n*folder:$OUTFOLDER\n*machine:$MACHINE" ntfy.sh/xISSztEV8EoOchM2
