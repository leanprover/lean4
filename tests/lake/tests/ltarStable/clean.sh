[ -f Test/A.lean.bak ] && mv -f Test/A.lean.bak Test/A.lean
rm -rf .lake lake-manifest.json out*.jsonl bundles*.txt staging*
