def main (xs : List String) : IO Unit :=
do
  b₁ ← IO.isDir xs.head;
  b₂ ← IO.fileExists xs.head;
  d₁ ← IO.appDir;
  d₂ ← IO.realPath ".";
  IO.println b₁;
  IO.println b₂;
  IO.println d₁;
  IO.println d₂
