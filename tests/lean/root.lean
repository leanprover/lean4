-*- mode: compilation; default-directory: "~/projects/lean4/build/release/" -*-
Compilation started at Mon Jun 13 13:56:14

/home/leodemoura/.elan/bin/lean  /home/leodemoura/projects/lean4/build/release/root.lean
Bla.f : Nat → Nat
/home/leodemoura/projects/lean4/build/release/root.lean:21:14: error: protected declarations must be in a namespace
/home/leodemoura/projects/lean4/build/release/root.lean:29:4: error: invalid declaration name `_root_`, `_root_` is a prefix used to refer to the 'root' namespace
/home/leodemoura/projects/lean4/build/release/root.lean:31:0: error: invalid namespace '_root_', '_root_' is a reserved namespace
/home/leodemoura/projects/lean4/build/release/root.lean:33:0: error: invalid namespace 'f._root_', '_root_' is a reserved namespace
/home/leodemoura/projects/lean4/build/release/root.lean:35:14: error: protected declarations must be in a namespace
/home/leodemoura/projects/lean4/build/release/root.lean:41:7: error: unknown identifier 'h'
/home/leodemoura/projects/lean4/build/release/root.lean:43:7: error: unknown identifier 'f'
f : Nat → Nat
_private.root.0.prv : Nat -> Nat
/home/leodemoura/projects/lean4/build/release/root.lean:90:48: error: unsolved goals
x : Nat
⊢ isEven (x + 1 + 1) = isEven x
/home/leodemoura/projects/lean4/build/release/root.lean:95:48: error: unsolved goals
x : Nat
⊢ isEven (x + 1 + 1) = isEven x

Compilation exited abnormally with code 1 at Mon Jun 13 13:56:14
