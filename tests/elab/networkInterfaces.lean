import Std.Net

#eval do
  let result ← Std.Net.interfaceAddresses
  assert! result.size > 0
