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
Use with e.g. GNU netcat to test in a browser:
```bash
$ nix-shell -p netcat-gnu --run "nc -lp 1234 -e ./build/bin/Webserver"
```
