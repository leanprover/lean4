partial def foo : Nat → Nat | n => foo n + 1
@[never_extract]
def main : IO Unit := IO.println $ Task.get $ Task.spawn fun _ => foo 0
