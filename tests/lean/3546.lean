/-!
Issue: "null characters break `readFile`/`getLine`"

When null characters are read from a file using `readFile`, the rest of the file is unexpectedly
cut off, instead of being read as a UTF-8 string (containing null characters).

When hex-dumped, traces of the rest of the file (e.g., the 'b' in "bar"; or corruptions, such as
0x0a) can sometimes be seen.
-/

def test : IO Unit := do
  let tmpFile := "3546.tmp"
  let s := "foo\u0000bar"
  IO.FS.writeFile tmpFile s
  let b := ← IO.FS.readBinFile tmpFile
  IO.println s!"s.length == {s.length}; b.size == {b.size}"
  let u := ← IO.FS.readFile tmpFile
  let v := if s == u then "good" else "bad"
  IO.println v

#eval test
