rm -rf .lake
lake exe "path with spaces"
# presence of this file should not break process spawn
touch .lake/build/bin/path
lake exe "path with spaces"
