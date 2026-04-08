rm -rf .lake/build
lake build release

# Create a named pipe for communication
PIPE="$TMP_DIR/pipe"
mkfifo "$PIPE"

# Run release in the background, redirect stdout to the pipe
.lake/build/bin/release > "$PIPE" &
PID=$!
echo "Started process with PID: $PID"

function await_line(){
  read -r line < "$PIPE"
  echo "Received line: $line"
  sleep 1
}

await_line
echo "Sending USR1 signal..."
kill -USR1 "$PID" 2>/dev/null || fail "Failed to send USR1"

await_line
echo "Sending HUP signal..."
kill -HUP "$PID" 2>/dev/null || fail "Failed to send HUP"

await_line
echo "Sending QUIT signal..."
kill -QUIT "$PID" 2>/dev/null || fail "Failed to send QUIT"

await_line
echo "Sending INT signal..."
kill -INT "$PID" 2>/dev/null || fail "Failed to send INT"

# Wait for process to finish
echo "Waiting for process $PID to finish..."
if wait "$PID"; then
    echo "Process completed successfully"
else
    fail "Process exited with code $?"
fi
