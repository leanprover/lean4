import DeprecatedArg.Def

-- Cross-file: old name produces warning
/--
warning: parameter `arg` of `f` has been deprecated, use `foo` instead

Hint: Rename this argument:
  a̵r̵g̵f̲o̲o̲
---
info: f 42 : Nat
-/
#guard_msgs in
#check f (arg := 42)

-- Cross-file: new name produces no warning
/--
info: f 42 : Nat
-/
#guard_msgs in
#check f (foo := 42)

-- Cross-file: positional arg produces no warning
/--
info: f 42 : Nat
-/
#guard_msgs in
#check f 42

-- Cross-file: multiple renames
/--
warning: parameter `old1` of `g` has been deprecated, use `new1` instead

Hint: Rename this argument:
  o̵l̵d̵n̲e̲w̲1
---
warning: parameter `old2` of `g` has been deprecated, use `new2` instead

Hint: Rename this argument:
  o̵l̵d̵n̲e̲w̲2
---
info: g 1 2 : Nat
-/
#guard_msgs in
#check g (old1 := 1) (old2 := 2)

-- Cross-file: disabling the linter rejects old names with a clean error
/--
error: Invalid argument name `arg` for function `f`

Hint: Perhaps you meant one of the following parameter names:
  • `foo`: a̵r̵g̵f̲o̲o̲
-/
#guard_msgs in
set_option linter.deprecated.arg false in
#check f (arg := 42)
