import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
A request line over a limit fails the same way however its bytes arrive: an error found at or past
`maxStartLineLength` is reported as that limit, as it is when the limit is reached before the error.
-/

def errorOf (config : Protocol.H1.Config) (parts : Array ByteArray) : Option Error := Id.run do
  let mut m : Machine .receiving := { config }
  for p in parts do
    m := m.feed p
    m := m.step.1
  return m.error

def bytewise (data : ByteArray) : Array ByteArray :=
  (Array.range data.size).map fun i => data.extract i (i + 1)

#eval show IO Unit from do
  let line := s!"OPTIONS /{String.ofList (List.replicate 30 'a')} HTTP/1.1\r\nHost: a\r\n\r\n".toUTF8
  -- The URI limit is reached past the start-line limit: both ways report the start-line limit.
  let config : Protocol.H1.Config := { maxStartLineLength := 20, maxUriLength := 16 }
  let whole := errorOf config #[line]
  let pieces := errorOf config (bytewise line)
  unless whole == pieces && whole == some .badMessage do
    throw <| IO.userError s!"start-line limit: whole {repr whole}, pieces {repr pieces}"
  -- The URI limit is reached first: both ways report it.
  let config : Protocol.H1.Config := { maxStartLineLength := 64, maxUriLength := 16 }
  let whole := errorOf config #[line]
  let pieces := errorOf config (bytewise line)
  unless whole == pieces && whole == some .uriTooLong do
    throw <| IO.userError s!"URI limit: whole {repr whole}, pieces {repr pieces}"
