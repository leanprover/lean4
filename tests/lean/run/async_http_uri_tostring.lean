import Std.Internal.Http.Protocol.H1.Parser

open Std.Http.Protocol

def runParser (parser : Std.Internal.Parsec.ByteArray.Parser α) (s : String) : IO α :=
  IO.ofExcept (parser.run s.toUTF8)

def parseCheck (s : String) (exact : String := s) : IO Unit := do
  let result ← runParser Std.Http.Parser.parseRequestTarget s
  if toString result = exact then
    pure ()
  else
    throw (.userError s!"expect {exact.quote} but got {(toString result).quote}")

#eval parseCheck "/path/with/encoded%20space"
#eval parseCheck "/path/with/encoded%20space/"
#eval parseCheck "*"
#eval parseCheck "https://ata/b?ata=be#lol%F0%9F%94%A5"
#eval parseCheck "/api/search?q=hello%20world&category=tech%2Bgames"
#eval parseCheck "/search?name=%E2%9C%93%20checked&emoji=%F0%9F%98%80"
#eval parseCheck "/api?param1=value1&param2=value2&param3=value3"
#eval parseCheck "/search?debug&verbose&q=test"
#eval parseCheck "/api?empty=&also_empty=&has_value=something"
#eval parseCheck "/search?q=cats%26dogs&filter=name%3Dmax"
#eval parseCheck "/"
#eval parseCheck "/api/v1/users/123/posts/456/comments/789"
#eval parseCheck "/files/../etc/passwd"
#eval parseCheck "/path%2Fwith%2Fencoded%2Fslashes"
#eval parseCheck "example.com:8080"
#eval parseCheck "https://example.com:8080/ata"
#eval parseCheck "192.168.1.1:3000"
#eval parseCheck "[::1]:8080"
#eval parseCheck "http://example.com/path/to/resource?query=value"
#eval parseCheck "https://api.example.com:443/v1/users?limit=10"
#eval parseCheck "http://[2001:db8::1]:8080/path"
#eval parseCheck "https://example.com/page#section1"
#eval parseCheck "/api?filters%5B%5D=active&filters%5B%5D=verified&sort%5Bname%5D=asc&sort%5Bdate%5D=desc"
#eval parseCheck "https://xn--nxasmq6b.xn--o3cw4h/path"
#eval parseCheck "localhost:65535"
#eval parseCheck "/"
#eval parseCheck "https://user:pass@secure.example.com/private"
#eval parseCheck "/?query=only"
#eval parseCheck "/double//slash//path"

-- Parse decode and encode of the paths differ. We can decode all percent encodings to human format and then
-- encode back using other rules that are the `pchar` parsing rules.

#eval parseCheck "/very/long/path/with/many/segments/and/encoded%20spaces/and%2Bplus%2Bsigns/final%2Fsegment"
                 "/very/long/path/with/many/segments/and/encoded%20spaces/and+plus+signs/final%2Fsegment"

#eval parseCheck "/files/my%20document%2Epdf"
                 "/files/my%20document.pdf"
