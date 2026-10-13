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
"$beam" --root "$project" doctor > "$TMP_DIR/doctor"
grep -q '^bundle source: toolchain$' "$TMP_DIR/doctor"
grep -q '^bundle ready: true$' "$TMP_DIR/doctor"

daemon=$(sed -n 's/^bundle daemon: //p' "$TMP_DIR/doctor")
plugin=$(sed -n 's/^plugin: //p' "$TMP_DIR/doctor")
owned_toolchain="$toolchain"
if command -v cygpath > /dev/null; then
    daemon=$(cygpath -u "$daemon")
    plugin=$(cygpath -u "$plugin")
    owned_toolchain=$(cygpath -u "$(cygpath -m "$toolchain")")
fi
case "$daemon" in "$owned_toolchain"/*) ;; *) fail "daemon outside relocated toolchain" ;; esac
case "$plugin" in "$owned_toolchain"/*) ;; *) fail "plugin outside relocated toolchain" ;; esac

mv "$daemon" "$daemon.saved"
capture_fail "$beam" --root "$project" doctor
check_out_contains 'missing Beam daemon'
mv "$daemon.saved" "$daemon"
mv "$plugin" "$plugin.saved"
capture_fail "$beam" --root "$project" doctor
check_out_contains 'missing Beam LSP plugin'
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
check_out_contains 'bundled lean-beam-mcp uses only its containing toolchain'
test ! -e "$TMP_DIR/missing-bundles"
test ! -e "$project/.beam/bundles"

# A project's toolchain selector must not silently load another Lean's plugin.
mkdir "$TMP_DIR/fake-bin"
printf '#!/usr/bin/env bash\necho /different/toolchain/bin/lean\n' > "$TMP_DIR/fake-bin/elan"
chmod +x "$TMP_DIR/fake-bin/elan"
printf 'different-toolchain\n' > "$project/lean-toolchain"
PATH="$TMP_DIR/fake-bin:$PATH" capture_fail "$beam" --root "$project" serve
check_out_matches 'project .*bundled Lean (toolchain|installation)'

matching_lean="$toolchain/bin/lean$exe_suffix"
if command -v cygpath > /dev/null; then
    matching_lean=$(cygpath -m "$matching_lean")
fi
printf '#!/usr/bin/env bash\nprintf "%%s\\n" "%s"\n' "$matching_lean" > "$TMP_DIR/fake-bin/elan"
PATH="$TMP_DIR/fake-bin:$PATH" "$beam" --root "$project" doctor > "$TMP_DIR/matching-doctor"
grep -q '^bundle ready: true$' "$TMP_DIR/matching-doctor"
