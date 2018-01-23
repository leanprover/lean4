import system.io
open io


def tst1 : io unit :=
do o ← stdout,
   -- fs.put_str_ln out "hello",
   fs.close o

#eval tst1
#eval tst1

def tst2 : io unit :=
do o ← stderr,
   -- fs.put_str_ln out "world",
   fs.close o

#eval tst2

def tst3 : io unit :=
do h ← mk_file_handle "io_fs_error.lean" io.mode.read,
   fs.close h,
   fs.close h

#eval tst3

def tst4 : io handle :=
mk_file_handle "bad_file_name.txt" io.mode.read

#eval tst4
