# Beam is built explicitly by release CI, like the external kernel checkers.
# LEAN_BEAM_REQUIRED=1 makes a missing executable fail; ordinary builds may skip.
exe_suffix=""
beam_prefix="${LEAN_BEAM_TEST_PREFIX:-$BUILD_DIR}"
[ ! -f "$beam_prefix/bin/lean-beam.exe" ] || exe_suffix=.exe
if [ ! -x "$beam_prefix/bin/lean-beam$exe_suffix" ]; then
    [ "${LEAN_BEAM_REQUIRED:-0}" = 0 ] || fail "lean-beam not built"
    echo "lean-beam not built; skipping"
    exit 0
fi
test -x "$beam_prefix/bin/lean-beam-mcp$exe_suffix" || fail "lean-beam-mcp not built"

python3 - "$beam_prefix" <<'PY_MANIFEST'
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys

prefix = Path(sys.argv[1])
record = json.loads((prefix / "lib/lean-beam/provenance.json").read_text())
assert record["schemaVersion"] == 3, "expected Beam provenance schema 3"
assert record["buildId"] and record["sourceCommit"] and record["payloadHash"]
frontends = record["components"]["frontends"]
target, = record["components"]["targets"]
assert target["compilerRevision"] == frontends["compilerRevision"]
expected = {frontends["cli"], frontends["mcp"], target["daemon"],
            target["plugin"], record["components"]["license"]}
destinations = set()
for artifact in record["artifacts"]:
    relative = PurePosixPath(artifact["destination"])
    assert not relative.is_absolute() and ".." not in relative.parts
    assert str(relative) not in destinations, relative
    destinations.add(str(relative))
    actual = hashlib.sha256((prefix / relative).read_bytes()).hexdigest()
    assert actual == artifact["hash"], f"Beam artifact hash mismatch: {relative}"
assert destinations == expected, "unexpected native Beam inventory"
PY_MANIFEST

# Exercise relocation without copying the standard library's large module tree.
toolchain="$TMP_DIR/toolchain with spaces"
mkdir -p "$toolchain/lib"
cp -R "$beam_prefix/bin" "$toolchain/bin"
for entry in "$beam_prefix"/lib/*; do
    if [ "$(basename "$entry")" = lean-beam ]; then
        cp -R "$entry" "$toolchain/lib/lean-beam"
    else
        ln -s "$entry" "$toolchain/lib/$(basename "$entry")"
    fi
done
beam="$toolchain/bin/lean-beam$exe_suffix"
mcp="$toolchain/bin/lean-beam-mcp$exe_suffix"
project="$TMP_DIR/project"
mkdir -p "$project"
printf 'name = "beam_smoke"\n' > "$project/lakefile.toml"
printf 'def answer : Nat := 42\n' > "$project/Main.lean"

owner_pid=""
cleanup_beam() {
    if [ -n "$owner_pid" ]; then
        "$beam" --root "$project" stop || true
        kill "$owner_pid" 2>/dev/null || true
        wait "$owner_pid" || true
    fi
    rm -rf "$TMP_DIR"
}
trap cleanup_beam EXIT

# Ambient standalone Beam installations must not affect the bundled runtime.
export BEAM_HOME="$TMP_DIR/missing-beam-home"
export BEAM_INSTALL_BUNDLE_DIR="$TMP_DIR/missing-bundles"
export BEAM_BUNDLE_DIR="$TMP_DIR/missing-bundles"
"$beam" --version | grep -q '^lean-beam '
"$beam" toolchain-build-info > "$TMP_DIR/build-info.json"
python3 - "$toolchain" "$TMP_DIR/build-info.json" <<'PY_BUILD_INFO'
import json
from pathlib import Path
import sys

record = json.loads((Path(sys.argv[1]) / "lib/lean-beam/provenance.json").read_text())
info = json.loads(Path(sys.argv[2]).read_text())
assert info["sourceRevision"] == record["sourceCommit"]
assert info["buildId"] == record["buildId"]
assert info["compiledLeanRevision"] == info["loadedLeanRevision"]
assert info["loadedLeanRevision"] == record["components"]["frontends"]["compilerRevision"]
PY_BUILD_INFO
"$beam" --root "$project" doctor > "$TMP_DIR/doctor"
grep -q '^target membership: present$' "$TMP_DIR/doctor"

daemon=$(sed -n 's/^bundle daemon: //p' "$TMP_DIR/doctor")
plugin=$(sed -n 's/^plugin: //p' "$TMP_DIR/doctor")
# macOS temporary directories may use a symlink such as /var -> /private/var.
owned_toolchain=$(cd "$toolchain" && pwd -P)
if command -v cygpath > /dev/null; then
    daemon=$(cygpath -u "$daemon")
    plugin=$(cygpath -u "$plugin")
    owned_toolchain=$(cygpath -u "$(cygpath -m "$owned_toolchain")")
fi
case "$daemon" in "$owned_toolchain"/*) ;; *) fail "daemon outside relocated toolchain" ;; esac
case "$plugin" in "$owned_toolchain"/*) ;; *) fail "plugin outside relocated toolchain" ;; esac

mv "$daemon" "$daemon.saved"
capture_fail "$beam" --root "$project" doctor
check_out_contains "$(basename "$daemon")"
mv "$daemon.saved" "$daemon"
mv "$plugin" "$plugin.saved"
capture_fail "$beam" --root "$project" doctor
check_out_contains "$(basename "$plugin")"
mv "$plugin.saved" "$plugin"

"$beam" --root "$project" serve > "$TMP_DIR/owner.out" 2> "$TMP_DIR/owner.err" &
owner_pid=$!
ready=0
for ((attempt = 0; attempt < 300; attempt++)); do
    if grep -q 'serving Beam session' "$TMP_DIR/owner.err"; then
        ready=1
        break
    fi
    kill -0 "$owner_pid" || break
    sleep 0.1
done
if [ "$ready" = 0 ]; then
    cat "$TMP_DIR/owner.err"
    fail "bundled Beam session did not start"
fi

"$beam" --root "$project" update Main.lean > "$TMP_DIR/update.json"
version=$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["result"]["version"])' "$TMP_DIR/update.json")
"$beam" --root "$project" run-at Main.lean "$version" 1 0 '#check answer' > "$TMP_DIR/probe.json"
python3 -c 'import json, sys; assert json.load(open(sys.argv[1]))["result"]["success"]' "$TMP_DIR/probe.json"
"$beam" --root "$project" stop
wait "$owner_pid"
owner_pid=""
test ! -e "$TMP_DIR/missing-bundles"
test ! -e "$project/.beam/bundles"

"$mcp" --version | grep -q '^lean-beam-mcp '
(cd "$project" && "$mcp" --self-check Main.lean) > "$TMP_DIR/mcp-check"
grep -q 'Lean Beam MCP self-check passed' "$TMP_DIR/mcp-check"
capture_fail "$mcp" --beam-cli /different/toolchain/bin/lean-beam --version
check_out_contains 'unexpected lean-beam-mcp argument'
test ! -e "$TMP_DIR/missing-bundles"
test ! -e "$project/.beam/bundles"

# Exercise unavailable selectors separately from existing foreign installations.
real_elan=$(command -v elan) || fail "elan is required for the installed-selector fixtures"
matching_prefix="$toolchain"
foreign_prefix="$beam_prefix"
elan_home="$TMP_DIR/elan-home"
if command -v cygpath > /dev/null; then
    matching_prefix=$(cygpath -m "$matching_prefix")
    foreign_prefix=$(cygpath -m "$foreign_prefix")
    elan_home=$(cygpath -m "$elan_home")
fi
export ELAN_HOME="$elan_home"
unset ELAN_TOOLCHAIN
"$real_elan" toolchain link beam-bundle-matching "$matching_prefix"
"$real_elan" toolchain link beam-bundle-foreign "$foreign_prefix"

printf 'beam-bundle-unavailable\n' > "$project/lean-toolchain"
capture_fail "$beam" --root "$project" serve
check_out_contains 'unavailable locally'

printf 'beam-bundle-foreign\n' > "$project/lean-toolchain"
capture_fail "$beam" --root "$project" serve
check_out_contains 'is not a member of this Beam installation'

printf 'beam-bundle-matching\n' > "$project/lean-toolchain"
"$beam" --root "$project" doctor > "$TMP_DIR/matching-doctor"
grep -q '^target membership: present$' "$TMP_DIR/matching-doctor"
test ! -e "$ELAN_HOME/toolchains/beam-bundle-unavailable"
