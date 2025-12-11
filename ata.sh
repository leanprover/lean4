#!/bin/bash

# Send HTTP/1.1 chunked request to localhost:8081
# Receives and prints server responses to stdout
# Stops when connection terminates or limit is reached

HOST="localhost"
PORT="8081"
counter=1
MAX_CHUNKS=1000  # Set to 0 for infinite, or any positive number for limit

# Create named pipes for bidirectional communication
REQUEST_PIPE="/tmp/http_request_$$"
RESPONSE_PIPE="/tmp/http_response_$$"

# Cleanup any existing pipes
rm -f $REQUEST_PIPE $RESPONSE_PIPE

# Create new pipes
mkfifo $REQUEST_PIPE
mkfifo $RESPONSE_PIPE

# Cleanup function
cleanup() {
    exec 3>&- 2>/dev/null
    exec 4<&- 2>/dev/null
    rm -f $REQUEST_PIPE $RESPONSE_PIPE
    kill $NC_PID 2>/dev/null
    kill $READER_PID 2>/dev/null
    exit
}

# Set trap for cleanup on exit
trap cleanup EXIT INT TERM

# Start netcat connection in background
nc $HOST $PORT < $REQUEST_PIPE > $RESPONSE_PIPE &
NC_PID=$!

# Start background process to read and print responses
cat $RESPONSE_PIPE &
READER_PID=$!

# Open pipe for writing
exec 3>$REQUEST_PIPE

# Send HTTP headers
echo -ne "POST /stream HTTP/1.1\r\n" >&3
echo -ne "Host: $HOST:$PORT\r\n" >&3
echo -ne "Transfer-Encoding: chunked\r\n" >&3
echo -ne "Content-Type: text/plain\r\n" >&3
echo -ne "\r\n" >&3

# Send chunks (infinite or limited)
while kill -0 $NC_PID 2>/dev/null; do
    # Check if limit is reached (if MAX_CHUNKS > 0)
    if [ $MAX_CHUNKS -gt 0 ] && [ $counter -gt $MAX_CHUNKS ]; then
        echo "Reached limit of $MAX_CHUNKS chunks. Sending final chunk." >&2
        # Send final zero-length chunk to end the chunked transfer
        printf "0\r\n\r\n" >&3
        break
    fi
    
    data="Chunk $counter: $(date '+%Y-%m-%d %H:%M:%S')\nData: $counter\n---\n"
    size=$(printf "%s" "$data" | wc -c)
    
    # Send chunk size in hex
    printf "%x\r\n" $size >&3
    # Send chunk data
    printf "%s\r\n" "$data" >&3
    
    ((counter++))
    sleep 0.5
done

# Wait a bit for final responses
sleep 1

echo "Connection terminated. Sent $((counter-1)) chunks." >&2