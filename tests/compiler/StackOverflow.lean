partial def foo : Nat → Nat | n => foo n + 1
@[neverExtract]
def main : IO Unit := IO.println $ foo 0
