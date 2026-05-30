Example of a super-simple web server using custom syntax for registering routes and emitting HTML

Compile with `lean --c=Webserver.c Webserver.lean && leanc -o Webserver Webserver.c` to get the
`./Webserver` executable listening on stdin and responding on stdout:
```bash
$ echo "GET /greet/me HTTP/1.1" | ./Webserver
HTTP/1.1 200 OK
Content-Type: text/html
Content-Length: 19

<h1>Hello, me!</h1>
```
Use with netcat to test in a browser at http://localhost:1234:
```bash
bash -c 'coproc nc -lp 1234; ./Webserver <&${COPROC[0]} >&${COPROC[1]}'
```
