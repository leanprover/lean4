#!/usr/bin/env bash

rm -rf .lake/build
lake build release

# Create a named pipe for communication
PIPE=$(mktemp -u)
mkfifo "$PIPE"

# Run release in the background, redirect stdout to the pipe
.lake/build/bin/release > "$PIPE" &
PID=$!

echo "Started process with PID: $PID"

# Read the first line from the pipe
{
    if read -r first_line < "$PIPE"; then
        echo "Received first line: $first_line"

        sleep 1

        echo "Sending USR1 signal..."
        kill -USR1 "$PID" 2>/dev/null || echo "Failed to send USR1"

        echo "Sending HUP signal..."
        kill -HUP "$PID" 2>/dev/null || echo "Failed to send HUP"

        echo "Sending QUIT signal..."
        kill -QUIT "$PID" 2>/dev/null || echo "Failed to send QUIT"

        echo "Sending INT signal..."
        kill -INT "$PID" 2>/dev/null || echo "Failed to send INT"
    else
        echo "Failed to read first line"
    fi
}

# Clean up the pipe
rm -f "$PIPE"

# Wait for process to finish
echo "Waiting for process $PID to finish..."
if wait "$PID"; then
    echo "Process completed successfully"
else
    echo "Process exited with code $?"
fi