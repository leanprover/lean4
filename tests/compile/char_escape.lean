module

def badString : String := "\x01abc"

public def main : IO Unit := do
  IO.println s!"length   = {badString.length}"
  IO.println s!"utf8Size = {badString.utf8ByteSize}"
  let ba := badString.toUTF8
  IO.println s!"toUTF8.size = {ba.size}"
  IO.print "bytes:"
  for i in 0...ba.size do IO.print s!" {ba[i]!}"
  IO.println ""
