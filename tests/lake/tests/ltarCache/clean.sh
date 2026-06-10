[ -f Test/A.lean.bak ] && mv -f Test/A.lean.bak Test/A.lean
rm -rf .lake lake-manifest.json produced.* out1.jsonl out2.jsonl \
  bundles1.txt bundles2.txt staging staging_bad staging_old
