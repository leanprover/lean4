/-! Stack overflow while inside the allocator must abort, not hang (#14992). -/

partial def loop (start : Nat) : Nat := start + loop (start + 1)

@[never_extract]
def main : IO Unit := IO.println (loop (2 ^ 64))
