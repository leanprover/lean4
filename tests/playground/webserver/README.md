Example of a super-simple web server using custom syntax for registering routes and emitting HTML

Compile with `leanmake bin` to get the `./build/bin/Webserver` executable listening on stdin and
responding on stdout:
```bash
$ echo "GET /greet/me HTTP/1.1" | ./build/bin/Webserver
HTTP/1.1 200 OK
Content-Type: text/html
Content-Length: 19

<h1>Hello, me!</h1>
```
Use with netcat to test in a browser at http://localhost:1234:
```bash
bash -c 'coproc nc -lp 1234; ./build/bin/Webserver <&${COPROC[0]} >&${COPROC[1]}'
```
