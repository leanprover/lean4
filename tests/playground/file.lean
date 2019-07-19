def main : IO Unit :=
do contents ← IO.readTextFile "file.lean";
   IO.println contents
