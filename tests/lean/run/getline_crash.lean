def tstGetLine (str : String) : IO Unit := do
let path := "tmp_file";
IO.FS.withFile path IO.FS.Mode.write $ λ (h : IO.FS.Handle) =>
  h.putStrLn str;
IO.FS.withFile path IO.FS.Mode.read $ λ (h : IO.FS.Handle) => do
  let str' ← h.getLine;
  IO.println str.length;
  IO.println str'.length;
  IO.print str';
  unless (str'.length == str.length + 1) do
    throw (IO.userError ("unexpected length: " ++ toString str'.trim.length));
  unless (str'.trim == str) do
    throw (IO.userError ("unexpected result: " ++ str'))

def tstGetLine2 (str1 str2 : String) : IO Unit := do
let path := "tmp_file";
IO.FS.withFile path IO.FS.Mode.write $ λ (h : IO.FS.Handle) => do {
  h.putStrLn str1; h.putStr str2
};
IO.FS.withFile path IO.FS.Mode.read $ λ (h : IO.FS.Handle) => do
  let str1' ← h.getLine;
  let str2' ← h.getLine;
  unless (str1'.length == str1.length + 1) do
    throw (IO.userError ("unexpected length: " ++ toString str1'.trim.length));
  unless (str1'.trim == str1) do
    throw (IO.userError ("unexpected result: " ++ str1'));
  unless (str2'.length == str2.length) do
    throw (IO.userError ("unexpected length: " ++ toString str2'.trim.length));
  unless (str2'.trim == str2) do
    throw (IO.userError ("unexpected result: " ++ str2'))

def tstGetLine3 (str : String) : IO Unit := do
  let path := "tmp_file";
  IO.FS.withFile path IO.FS.Mode.write $ λ (h : IO.FS.Handle) => do {
    h.putStrLn str
  };
  IO.FS.withFile path IO.FS.Mode.read $ λ (h : IO.FS.Handle) => do
    (h.getLine >>= IO.println);
    (h.getLine >>= IO.println);
    (h.getLine >>= IO.println);
    IO.print "done";
    pure ()

/--
info: abc



done
-/
#guard_msgs in
#eval tstGetLine3 "abc"

/--
info: 40
41
αααααααααααααααααααααααααααααααααααααααα
-/
#guard_msgs in
#eval tstGetLine ("".pushn 'α' 40)

/--
info: 1
2
a
-/
#guard_msgs in
#eval tstGetLine "a"

/--
info: 0
1
-/
#guard_msgs in
#eval tstGetLine ""

/--
info: 20
21
αααααααααααααααααααα
-/
#guard_msgs in
#eval tstGetLine ("".pushn 'α' 20)

/--
info: 61
62
aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
-/
#guard_msgs in
#eval tstGetLine ("".pushn 'a' 61)

/--
info: 61
62
ααααααααααααααααααααααααααααααααααααααααααααααααααααααααααααα
-/
#guard_msgs in
#eval tstGetLine ("".pushn 'α' 61)

/--
info: 62
63
aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
-/
#guard_msgs in
#eval tstGetLine ("".pushn 'a' 62)

/--
info: 63
64
aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
-/
#guard_msgs in
#eval tstGetLine ("".pushn 'a' 63)

/--
info: 64
65
aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
-/
#guard_msgs in
#eval tstGetLine ("".pushn 'a' 64)

/--
info: 65
66
aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
-/
#guard_msgs in
#eval tstGetLine ("".pushn 'a' 65)

/--
info: 66
67
aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
-/
#guard_msgs in
#eval tstGetLine ("".pushn 'a' 66)

/--
info: 128
129
aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
-/
#guard_msgs in
#eval tstGetLine ("".pushn 'a' 128)

#guard_msgs in
#eval tstGetLine2 ("".pushn 'α' 20) ("".pushn 'β' 20)

#guard_msgs in
#eval tstGetLine2 ("".pushn 'α' 40) ("".pushn 'β' 40)

#guard_msgs in
#eval tstGetLine2 ("".pushn 'a' 61) ("".pushn 'b' 61)

#guard_msgs in
#eval tstGetLine2 ("".pushn 'a' 61) ("".pushn 'b' 62)
