#!/usr/bin/env bash
# Fake file worker for `closed_stdout_worker.lean`. It closes its stdout and discards all messages,
# including the `exit` notification. It only exits when its stdin is closed.
exec >&-
cat > /dev/null
