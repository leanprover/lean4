import system.io
open io


def mk_test_file : io unit :=
do h ← mk_file_handle "io_fs.txt" io.mode.write,
   fs.put_str_ln h "hello world",
   fs.put_str_ln h "hello world again",
   fs.close h

def read_test_file : io string :=
do b ← fs.read_file "io_fs.txt",
   return b^.to_string

#eval do
  mk_test_file,
  c ← read_test_file,
  put_str c,
  if c = "hello world\nhello world again\n" then return ()
  else io.fail "file content does not match expected result"
