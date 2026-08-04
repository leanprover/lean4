# TLS test certificate fixtures

Self-signed certificates used by the `async_ssl_*` tests. These contain **no secrets**: the
private key exists only so the tests can drive a real TLS handshake, and nothing outside the
test suite trusts these certificates. They are committed as fixtures (instead of generated at
test time) so the tests neither shell out to the `openssl` CLI nor depend on it being
installed — subprocess spawning in these tests also produced spurious LeakSanitizer reports
in the sanitizer CI build.

All certificates are signed by `key.pem` (RSA-2048) and are valid until 2126, except
`expired.pem`, whose validity window is entirely in 2020 (used to verify that expired
certificates are rejected).

| file | subject | notes |
|---|---|---|
| `key.pem` | | RSA-2048 private key for all certs below |
| `cert.pem` | `CN=localhost` | standard server cert (no SAN; hostname matching uses the CN fallback) |
| `wildcard.pem` | `CN=*.test.local` | SAN: `DNS:*.test.local, DNS:test.local` |
| `multisan.pem` | `CN=alpha.test.local` | SAN: `DNS:alpha.test.local, DNS:beta.test.local` |
| `expired.pem` | `CN=localhost` | valid 2020-01-01 → 2020-01-02 only |

To regenerate:

```sh
openssl genrsa -out key.pem 2048
openssl req -new -x509 -key key.pem -out cert.pem -days 36500 -subj "/CN=localhost"
openssl req -new -x509 -key key.pem -out wildcard.pem -days 36500 -subj "/CN=*.test.local" \
  -addext "subjectAltName=DNS:*.test.local,DNS:test.local"
openssl req -new -x509 -key key.pem -out multisan.pem -days 36500 -subj "/CN=alpha.test.local" \
  -addext "subjectAltName=DNS:alpha.test.local,DNS:beta.test.local"
openssl req -new -key key.pem -out expired.csr -subj "/CN=localhost"
openssl x509 -req -in expired.csr -signkey key.pem -out expired.pem -set_serial 99 \
  -not_before 20200101000000Z -not_after 20200102000000Z && rm expired.csr
```
