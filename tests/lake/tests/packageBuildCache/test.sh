#!/usr/bin/env bash
source ../common.sh

./clean.sh

PYTHON="${PYTHON:-python3}"
if ! "$PYTHON" -c 'import sys; sys.exit(sys.version_info < (3, 11))' 2> /dev/null; then
  echo "SKIPPED: $PYTHON 3.11 or later not found"
  exit 0
fi

TEST_DIR="$(norm_path "$(pwd)")"
WORK_DIR="$TEST_DIR/work"
STORE_DIR="$WORK_DIR/store"
CACHE_DIR="$WORK_DIR/cache"
SERVER_LOG="$WORK_DIR/server.log"
PORT_FILE="$WORK_DIR/port"
mkdir -p "$WORK_DIR/dep/Dep" "$STORE_DIR"

"$PYTHON" ../cacheTransfer/server.py --store "$STORE_DIR" --port-file "$PORT_FILE" \
  >> "$SERVER_LOG" 2>&1 &
SERVER_PID=$!
trap 'kill "$SERVER_PID" 2> /dev/null || true' EXIT
while [ ! -s "$PORT_FILE" ]; do
  if ! kill -0 "$SERVER_PID" 2> /dev/null; then
    cat "$SERVER_LOG"
    exit 1
  fi
  sleep 0.1
done
URL="http://127.0.0.1:$(cat "$PORT_FILE")/ok"
cd "$WORK_DIR"

# No system cache service or environment endpoint configuration is needed.
touch no-services.toml
export LAKE_CONFIG="$WORK_DIR/no-services.toml"
export LAKE_CACHE_DIR="$CACHE_DIR"
export ELAN_TOOLCHAIN=
unset LAKE_ARTIFACT_CACHE LAKE_CACHE_ARTIFACT_ENDPOINT LAKE_CACHE_REVISION_ENDPOINT
export RESERVOIR_API_URL="$URL/api/v1"

cat > dep/lakefile.toml << EOF
name = "dep"
buildCache = "$URL/"
platformIndependent = true
[[lean_lib]]
name = "Dep"
globs = ["Dep.*"]
EOF
touch dep/Dep.lean
printf 'module\npublic def used : Nat := 7\n' > dep/Dep/Used.lean
printf 'module\npublic def unused : Nat := 9\n' > dep/Dep/Unused.lean
(
  cd dep
  init_git
  git remote add origin https://github.com/leanprover/package-build-cache.git
)
REV="$(git -C dep rev-parse HEAD)"

cat > lakefile.toml << EOF
name = "consumer"
defaultTargets = ["Test"]
[[require]]
name = "dep"
path = "dep"
[[lean_lib]]
name = "Test"
EOF
cat > Test.lean << EOF
import Dep.Used
example : used = 7 := rfl
EOF

# Publish two modules. Building the cache owner itself must not contact its cache.
: > "$SERVER_LOG"
LAKE_ARTIFACT_CACHE=true test_run -d dep build Dep -o outputs.jsonl
test_exp ! -s "$SERVER_LOG"
mkdir -p "$STORE_DIR/revisions/leanprover/package-build-cache"
cp outputs.jsonl "$STORE_DIR/revisions/leanprover/package-build-cache/$REV.jsonl"
mkdir -p "$STORE_DIR/artifacts/leanprover/package-build-cache"
for art in "$CACHE_DIR"/artifacts/*.ltar; do
  name="$(basename "$art" .ltar)"
  cp "$art" "$STORE_DIR/artifacts/leanprover/package-build-cache/$name.art"
done

reset_consumer() {
  # Lake's clean command removes only the fixture's build outputs.
  test_run -d dep clean
  test_run clean
  test_run cache clean
  : > "$SERVER_LOG"
}

reset_consumer
# A downstream default build discovers mappings and downloads only its import.
test_out 'downloaded artifact' build
match_text "$URL/artifacts/" produced.out
test_exp -f dep/.lake/build/lib/lean/Dep/Used.olean
test_exp ! -e dep/.lake/build/lib/lean/Dep/Unused.olean
test_cmd_eq 1 grep -c 'GET /ok/revisions/' "$SERVER_LOG"
test_cmd_eq 1 grep -c 'GET /ok/artifacts/' "$SERVER_LOG"
test_exp -z "$(find "$CACHE_DIR/revisions" -name '*.attempt' -print)"
test_run -d dep build +Dep.Used --no-build

# Repeated builds need neither network requests nor local compilation.
: > "$SERVER_LOG"
test_run build --no-build
test_exp ! -s "$SERVER_LOG"

# A second imported module reuses the mappings and fetches just its own archive.
test_out 'downloaded artifact' -v build @dep/+Dep.Unused --no-build
test_cmd_eq 1 grep -c 'GET /ok/artifacts/' "$SERVER_LOG"
no_match_text 'GET /ok/revisions/' "$SERVER_LOG"

# Disabling automatic downloads also disables them with already cached mappings.
test_run -d dep clean
test_run clean
rm -f "$CACHE_DIR"/artifacts/*
: > "$SERVER_LOG"
test_out 'Built Dep.Used' --no-cache -v build
test_exp ! -s "$SERVER_LOG"

reset_consumer
test_out 'Built Dep.Used' --no-cache -v build
test_exp ! -s "$SERVER_LOG"

# The environment can disable discovery when the package leaves its cache setting unset.
reset_consumer
LAKE_ARTIFACT_CACHE=false test_out 'Built Dep.Used' -v build
test_exp ! -s "$SERVER_LOG"

# The global download switches also work when the dependency enables its cache.
cp dep/lakefile.toml dep-config.toml
{ echo 'enableArtifactCache = true'; cat dep-config.toml; } > dep/lakefile.toml
reset_consumer
test_out 'downloaded artifact' build
match_text "$URL/artifacts/" produced.out
reset_consumer
test_out 'Built Dep.Used' --no-cache build
test_exp ! -s "$SERVER_LOG"
reset_consumer
LAKE_NO_CACHE=true test_out 'Built Dep.Used' build
test_exp ! -s "$SERVER_LOG"
cp dep-config.toml dep/lakefile.toml

# Missing revision mappings are an optional cache miss, not a build failure.
reset_consumer
mv "$STORE_DIR/revisions" "$WORK_DIR/saved-revisions"
test_out 'Built Dep.Used' -v build
test_cmd_eq 1 grep -c 'GET /ok/revisions/' "$SERVER_LOG"
no_match_text 'GET /ok/artifacts/' "$SERVER_LOG"
: > "$SERVER_LOG"
test_run build --no-build
test_exp ! -s "$SERVER_LOG"
# After the retry interval, newly published mappings can be discovered.
"$PYTHON" - "$CACHE_DIR" << 'PY'
import os, pathlib, sys
for path in pathlib.Path(sys.argv[1]).rglob('*.attempt'):
    os.utime(path, (1, 1))
PY
: > "$SERVER_LOG"
test_run build
test_cmd_eq 1 grep -c 'GET /ok/revisions/' "$SERVER_LOG"
mv "$WORK_DIR/saved-revisions" "$STORE_DIR/revisions"

# Missing artifacts and corrupted artifacts both fall back to compilation.
reset_consumer
mv "$STORE_DIR/artifacts" "$WORK_DIR/saved-artifacts"
test_out 'Built Dep.Used' -v build
test_cmd_eq 1 grep -c 'GET /ok/artifacts/' "$SERVER_LOG"
mv "$WORK_DIR/saved-artifacts" "$STORE_DIR/artifacts"

reset_consumer
cp -r "$STORE_DIR/artifacts" "$WORK_DIR/saved-artifacts"
for art in "$STORE_DIR"/artifacts/leanprover/package-build-cache/*.art; do
  chmod u+w "$art"
  echo corrupt > "$art"
done
test_out 'Built Dep.Used' -v build
match_text 'hash mismatch' produced.out
mv "$STORE_DIR/artifacts" "$WORK_DIR/corrupt-artifacts"
mv "$WORK_DIR/saved-artifacts" "$STORE_DIR/artifacts"

# Untrusted artifact paths cannot overwrite files outside the cache.
reset_consumer
MAPPING="$STORE_DIR/revisions/leanprover/package-build-cache/$REV.jsonl"
cp "$MAPPING" saved.jsonl
"$PYTHON" - "$MAPPING" << 'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
contents = path.read_text()
assert '.ltar"' in contents
path.write_text(contents.replace('.ltar"', '.ltar/../../../pwn/escaped.ltar"'))
PY
mkdir -p pwn
echo untouched > pwn/escaped.ltar
test_out 'Built Dep.Used' -v build
test_cmd_eq untouched cat pwn/escaped.ltar
no_match_text 'GET /ok/artifacts/' "$SERVER_LOG"
cp saved.jsonl "$MAPPING"

# Mapping retrieval must also work when the dependency build directory exists.
reset_consumer
mkdir -p dep/.lake/build
test_out 'downloaded artifact' -v build

# Cached mappings cannot cause modified source to use an obsolete artifact.
reset_consumer
echo 'def extra : Nat := 11' >> dep/Dep/Used.lean
test_out 'Built Dep.Used' -v build
no_match_text 'GET /ok/artifacts/' "$SERVER_LOG"
git -C dep checkout -- Dep/Used.lean

# SSH remotes identify the same published repository scope.
reset_consumer
git -C dep remote set-url origin git@github.com:leanprover/package-build-cache.git
test_out 'downloaded artifact' -v build

# Trailing slashes in GitHub remotes do not become part of the repository scope.
for remote in \
  https://github.com/leanprover/package-build-cache.git/ \
  https://github.com/leanprover/package-build-cache/// \
  ssh://git@github.com/leanprover/package-build-cache.git/; do
  reset_consumer
  git -C dep remote set-url origin "$remote"
  test_out 'downloaded artifact' -v build
  match_text "GET /ok/revisions/leanprover/package-build-cache/$REV.jsonl" "$SERVER_LOG"
done

# Revision metadata is separated by toolchain even in a shared LAKE_CACHE_DIR.
# Keep the unqualified mapping installed so that an incorrect cache key hides the request.
test_run -d dep clean
test_run clean
rm -f "$CACHE_DIR"/artifacts/*
: > "$SERVER_LOG"
mkdir -p "$STORE_DIR/revisions/leanprover/package-build-cache/tc/cache-test"
cp outputs.jsonl "$STORE_DIR/revisions/leanprover/package-build-cache/tc/cache-test/$REV.jsonl"
ELAN_TOOLCHAIN=cache-test test_out 'downloaded artifact' -v build
match_text "/tc/cache-test/$REV.jsonl" "$SERVER_LOG"

# The field survives both TOML and Lean configuration decoding/translation.
test_run -d dep translate-config lean translated.produced.lean
test_run -d dep -f "$WORK_DIR/translated.produced.lean" translate-config toml translated.produced.toml
match_text "buildCache = \"$URL/\"" translated.produced.toml

# Changing the declared endpoint must replace obsolete remote service references,
# while keeping previously installed local outputs usable.
test_run -d dep clean
test_run clean
rm -f "$CACHE_DIR"/artifacts/*
: > "$SERVER_LOG"
mkdir -p "$STORE_DIR/mirror"
cp -r "$STORE_DIR/revisions" "$STORE_DIR/artifacts" "$STORE_DIR/mirror/"
sed_i "s|buildCache = \"$URL/\"|buildCache = \"$URL/mirror\"|" dep/lakefile.toml
test_out 'downloaded artifact' -v build
match_text 'GET /ok/mirror/artifacts/' "$SERVER_LOG"

# Switching endpoints within the retry interval reuses both downloaded mappings.
find "$CACHE_DIR/revisions" -name '*.jsonl' -exec sh -c 'touch "$1.attempt"' _ {} \;
for endpoint in "$URL/" "$URL/mirror"; do
  test_run -d dep clean
  test_run clean
  rm -f "$CACHE_DIR"/artifacts/*
  : > "$SERVER_LOG"
  sed_i "s|^buildCache = .*|buildCache = \"$endpoint\"|" dep/lakefile.toml
  test_out 'downloaded artifact' build
  match_text "${endpoint%/}/artifacts/" produced.out
  no_match_text '/revisions/' "$SERVER_LOG"
done

# Once installed, revision mappings are not scanned again on a no-op build.
find "$CACHE_DIR/revisions" -name '*.jsonl' -exec sh -c 'echo invalid > "$1"' _ {} \;
: > "$SERVER_LOG"
test_not_out 'invalid' -v build --no-build
test_exp ! -s "$SERVER_LOG"

# Malformed successful responses are not retained as revision mappings.
reset_consumer
cp "$STORE_DIR/mirror/revisions/leanprover/package-build-cache/$REV.jsonl" saved.jsonl
echo '<html>unavailable</html>' > "$STORE_DIR/mirror/revisions/leanprover/package-build-cache/$REV.jsonl"
test_out 'Built Dep.Used' -v build
test_exp -z "$(find "$CACHE_DIR/revisions" -name '*.jsonl' -print)"
cp saved.jsonl "$STORE_DIR/mirror/revisions/leanprover/package-build-cache/$REV.jsonl"
"$PYTHON" - "$CACHE_DIR" << 'PY'
import os, pathlib, sys
for path in pathlib.Path(sys.argv[1]).rglob('*.attempt'):
    os.utime(path, (1, 1))
PY
test_run -d dep clean
test_run clean
test_out 'downloaded artifact' -v build

# Concurrent workspaces share mapping installation and never see partial artifacts.
reset_consumer
mkdir -p "$WORK_DIR/other"
cp lakefile.toml Test.lean "$WORK_DIR/other/"
cp -r dep "$WORK_DIR/other/dep"
"$LAKE" build > concurrent-a.log 2>&1 &
BUILD_A=$!
"$LAKE" -d "$WORK_DIR/other" build > concurrent-b.log 2>&1 &
BUILD_B=$!
test_cmd wait "$BUILD_A"
test_cmd wait "$BUILD_B"
test_cmd_eq 1 grep -c 'GET /ok/mirror/revisions/' "$SERVER_LOG"
test_exp -z "$(find "$CACHE_DIR/artifacts" -name '*.tmp' -print)"

# Returning to a previously installed endpoint restores its service references.
test_run -d dep clean
test_run clean
rm -f "$CACHE_DIR"/artifacts/*
: > "$SERVER_LOG"
sed_i "s|buildCache = \"$URL/mirror\"|buildCache = \"$URL/\"|" dep/lakefile.toml
test_out 'downloaded artifact' -v build
match_text 'GET /ok/artifacts/' "$SERVER_LOG"
