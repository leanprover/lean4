[ -f Test/A.lean.bak ] && mv -f Test/A.lean.bak Test/A.lean
rm -rf .lake lake-manifest.json produced.* out*.jsonl bundles*.txt \
  staging staging_bad staging_old staging8
