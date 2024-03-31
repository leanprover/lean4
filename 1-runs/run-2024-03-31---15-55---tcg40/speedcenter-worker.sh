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

COMMITS=("2024-borrowing-benching-baseline" "2024-03-30--15-19--tcg40")
KINDS=("noreuse" "reuse")

for i in {0..1}; do
  echo "@@@ ${KINDS[i]} BENCH @@@"
  CSVNAME="${KINDS[i]}.stage3.csv"
  PROFILE_FILE=$EXPERIMENTDIR/$CSVNAME
  mv "$PROFILE_FILE" $(basename "$PROFILE_FILE" .csv).pre-suite-bench.csv || true # move old profile file if it exists.

  # link lean tooolchain
  # # https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/elan.20toolchain.20link.3A.20three.20hyphens.20becomes.20colon.3F/near/430447189
  # # Lean toolchain does not like having three dash, so for now, just name it based on KINDS.
  LEAN_TOOLCHAIN="${KINDS[i]}"
  # TODO: elan does not like '---' in folder name?
  elan toolchain link "$LEAN_TOOLCHAIN" "$EXPERIMENTDIR/builds/${KINDS[i]}/build/release/stage2"
  cd $EXPERIMENTDIR/builds/${KINDS[i]}/tests/bench/
  elan override set $LEAN_TOOLCHAIN # set override for temci
  elan show # show the toolchain.
  temci exec --config speedcenter.yaml --out "$EXPERIMENTDIR/${KINDS[i]}.speedcenter.bench.yaml" --included_blocks suite # run temci
  curl -d "Done[BENCH-${KINDS[i]}]. run:$EXPERIMENTDIR. machine:$(uname -a)."  ntfy.sh/xISSztEV8EoOchM2
done;
