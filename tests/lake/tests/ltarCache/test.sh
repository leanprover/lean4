#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Hermetic, workspace-local artifact cache: an empty `LAKE_CACHE_DIR` disables the
# system cache, so all artifacts and mappings live under `.lake/cache`. The package
# enables the artifact cache and `restoreAllArtifacts` (see lakefile.toml).
export LAKE_CACHE_DIR=

# Extract the set of bundle (`.ltar`) content hashes referenced by a mapping file.
bundles() { grep -oE '[0-9a-f]{16}\.ltar' "$1" | sort -u; }

#-------------------------------------------------------------------------------
echo "# 1. A build populates the cache and emits a mapping whose entries pair a"
echo "#    bundle reference with its recorded output hashes."
#-------------------------------------------------------------------------------
test_run build -o out1.jsonl
test_cmd ls .lake/cache/artifacts/*.ltar
bundles out1.jsonl > bundles1.txt
test_exp -s bundles1.txt
# Each mapping entry is [inputHash, "<bundle>.ltar", {outputs}]: the second element
# is the bare bundle reference (readable by older Lake) and the third carries the
# recorded output hashes.
test_cmd python3 -c '
import json
seen = False
for ln in open("out1.jsonl"):
    ln = ln.strip()
    if not ln.startswith("["): continue
    a = json.loads(ln)
    assert isinstance(a[1], str) and a[1].endswith(".ltar"), a
    assert len(a) == 3 and isinstance(a[2], dict) and "o" in a[2], a
    seen = True
assert seen, "no mapping entries found"
print("mapping entry shape OK: data=bundle ref + recorded outputs")
'

#-------------------------------------------------------------------------------
echo "# 2. Bundles are content-stable: a comment-only edit changes the input"
echo "#    hash but no output, so every bundle hash is unchanged. (Older Lake"
echo "#    embeds the input hash in the bundle, so every bundle would change.)"
#-------------------------------------------------------------------------------
cp Test/A.lean Test/A.lean.bak
printf '\n-- a cosmetic comment; does not change any output\n' >> Test/A.lean
test_run build -o out2.jsonl
bundles out2.jsonl > bundles2.txt
# The set of bundle content hashes is identical across the edit ...
test_cmd diff bundles1.txt bundles2.txt
# ... even though the mapping itself changed (the edited module's input hash moved).
test_cmd_fails diff out1.jsonl out2.jsonl

#-------------------------------------------------------------------------------
echo "# 3. Staging from the mapping collects only bundles; the recorded output"
echo "#    hashes are metadata, not upload targets."
#-------------------------------------------------------------------------------
test_run cache stage out2.jsonl staging
test_cmd ls staging/*.ltar
test_cmd_fails ls staging/*.olean
test_cmd_fails ls staging/*.ilean
test_cmd_fails ls staging/*.c

#-------------------------------------------------------------------------------
echo "# 4. Distribution consume: a cache holding only bundles + mappings must fetch,"
echo "#    unpack, and verify the bundle against the recorded outputs."
#-------------------------------------------------------------------------------
rm -rf .lake/cache .lake/build
test_run cache unstage staging
test_cmd_fails ls .lake/cache/artifacts/*.olean   # no individual artifacts present
test_out "leantar" build -v                       # bundles are unpacked
test_run build --no-build --rehash                # outputs verify as up-to-date

#-------------------------------------------------------------------------------
echo "# 5. Integrity: a mapping entry whose recorded outputs disagree with the bundle"
echo "#    is rejected with a warning rather than silently trusted; the build"
echo "#    self-heals by rebuilding and overwriting the offending entry."
#-------------------------------------------------------------------------------
rm -rf .lake/cache .lake/build
python3 - <<'PY'
import json, shutil
from pathlib import Path
src, dst = Path("staging"), Path("staging_bad")
shutil.rmtree(dst, ignore_errors=True); shutil.copytree(src, dst)
f = dst / "outputs.jsonl"; out = []
for ln in f.read_text().splitlines():
    s = ln.strip()
    if s.startswith("["):
        a = json.loads(s)
        if len(a) > 2 and isinstance(a[2], dict) and a[2].get("o"):
            a[2]["o"][0] = "deadbeefdeadbeef.olean"   # corrupt a recorded output hash
        out.append(json.dumps(a))
    else:
        out.append(ln)
f.write_text("\n".join(out) + "\n")
PY
test_run cache unstage staging_bad
test_out "cache integrity error" build
test_not_out "cache integrity error" build --no-build --rehash

#-------------------------------------------------------------------------------
echo "# 6. Backward compatible: an older mapping entry (bundle reference only, no"
echo "#    recorded outputs) is consumed without verification and without error."
#-------------------------------------------------------------------------------
rm -rf .lake/cache .lake/build
python3 - <<'PY'
import json, shutil
from pathlib import Path
src, dst = Path("staging"), Path("staging_old")
shutil.rmtree(dst, ignore_errors=True); shutil.copytree(src, dst)
f = dst / "outputs.jsonl"; out = []
for ln in f.read_text().splitlines():
    s = ln.strip()
    if s.startswith("["):
        a = json.loads(s)[:2]   # drop the recorded-outputs element -> old 2-element form
        out.append(json.dumps(a))
    else:
        out.append(ln)
f.write_text("\n".join(out) + "\n")
PY
test_run cache unstage staging_old
test_not_out "cache integrity error" build
test_run build --no-build --rehash

#-------------------------------------------------------------------------------
echo "# 7. With recorded outputs and a warm artifact cache, a bundle mapping entry"
echo "#    is served from the individually cached artifacts without unpacking."
#-------------------------------------------------------------------------------
# Step 6 left the individual artifacts in the cache; rewrite the mappings back to
# bundle-reference form and wipe the build directory. The recorded outputs resolve
# locally, so no bundle is unpacked.
rm -rf .lake/build
test_run cache unstage staging
test_not_out "leantar" build -v
test_run build --no-build --rehash

./clean.sh
echo "ltarCache: all checks passed"
