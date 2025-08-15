#!/usr/bin/env bash

rm -rf .lake/build

# Run the process in the background
lake build release
.lake/build/bin/release &
PID=$!

sleep 1

# Send SIGUSR1 4
kill -s USR1 "$PID"
sleep 0.2

# Send SIGHUP 2
kill -s HUP "$PID"
sleep 0.2

# Send SIGQUIT 3
kill -s QUIT "$PID"
sleep 0.2

# Send SIGINT 1
kill -s INT "$PID"
sleep 0.2

# Wait for the process to handle the signal
wait "$PID"
