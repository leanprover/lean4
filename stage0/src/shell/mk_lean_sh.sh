#!/bin/sh
# Auxiliary script that creates the file `lean.sh` if it doesn't
# exist yet
DEST=$1
if [ -x "$DEST/lean.sh" ]; then
    # Nothing to be done, file already exists
    exit 0
else
    cat > "$DEST/lean.sh" <<EOF
if ! "$DEST/lean" \$* ; then echo "FAILED: \$*"; exit 1; fi
EOF
    chmod +x "$DEST/lean.sh"
fi
