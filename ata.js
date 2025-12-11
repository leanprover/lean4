const net = require('net');

// Configuration
const HOST = 'localhost';
const PORT = 8081;
const MAX_CHUNKS = 100; // Set to 0 for infinite, or any positive number for limit
const DELAY = 500; // Delay between chunks in milliseconds

let counter = 1;

// Create TCP connection
const client = net.createConnection({ host: HOST, port: PORT }, () => {
    console.error('Connected to server');

    // Send HTTP headers
    client.write('POST /stream HTTP/1.1\r\n');
    client.write(`Host: ${HOST}:${PORT}\r\n`);
    client.write('Transfer-Encoding: chunked\r\n');
    client.write('Content-Type: text/plain\r\n');
    client.write('\r\n');

    // Start sending chunks
    sendChunk();
});

// Receive and print server responses
client.on('data', (data) => {
    process.stdout.write(data);
});

client.on('end', () => {
    console.error(`\nConnection terminated. Sent ${counter - 1} chunks.`);
    process.exit(0);
});

client.on('error', (err) => {
    console.error('Connection error:', err.message);
    process.exit(1);
});

function sendChunk() {
    // Check if limit is reached
    if (MAX_CHUNKS > 0 && counter > MAX_CHUNKS) {
        console.error(`Reached limit of ${MAX_CHUNKS} chunks. Sending final chunk.`);
        // Send final zero-length chunk to end the chunked transfer
        client.write('0\r\n\r\n');
        // Give time for server to respond before closing
        setTimeout(() => client.end(), 1000);
        return;
    }

    // Prepare chunk data
    const data = `Chunk ${counter}: ${new Date().toISOString()}\nData: ${counter}\n---\n`;
    const size = Buffer.byteLength(data);

    // Send chunk size in hex
    client.write(`${size.toString(16)}\r\n`);
    // Send chunk data
    client.write(`${data}\r\n`);

    console.log("Sent")

    counter++;

    // Schedule next chunk
    setTimeout(sendChunk, DELAY);
}

// Handle Ctrl+C gracefully
process.on('SIGINT', () => {
    console.error('\nInterrupted. Closing connection...');
    client.end();
    process.exit(0);
});