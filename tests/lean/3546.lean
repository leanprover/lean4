/-!
Issue: "null characters break `readFile`/`getLine`"

When null characters are read from a file using `readFile`, the rest of the file is unexpectedly
cut off, instead of being read as a UTF-8 string (containing null characters).

When hex-dumped, traces of the rest of the file (e.g., the 'b' in "bar"; or corruptions, such as
0x0a) can sometimes be seen.
-/

def test : IO Unit := do
  let tmpFile := "3546.tmp"
  let s := "foo\u0000bar\ngoo\u0000g\
  0123456789abcdef\
  0123456789abcdef\
  0123456789abcdef\
  0123456789abcdef\
  0123456789abcdef\
  0123456789abcdef\
  0123456789abcdef\
  0123456789abcdef\
  0123456789abcdef\\n
  012345\u0000789abcdef\
  0123456789abcdef\
  0123456789abcdef\
  0123456789abcdef\
  0123456789\u0000bcdef\
  0123456789abcdef\
  0123456789abcdef\
  01\u0000\u0000456789abcdef\
  0123456789abcdef\
  \n\n\u0000h"
  let s' := List.toByteArray $ List.map (λ x => UInt8.ofNat $ x.val.val) s.data
  IO.FS.writeBinFile tmpFile s'
  let b := ← IO.FS.readBinFile tmpFile
  IO.println s!"s.length == {s.length}; b.size == {b.size}"
  let u := ← IO.FS.readFile tmpFile
  let v := if s == u then "good" else "bad"
  IO.println v

#eval test
