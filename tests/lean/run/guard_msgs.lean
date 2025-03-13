import Lean.Elab.Command

#guard_msgs in
/-- error: unknown identifier 'x' -/
#guard_msgs in
example : α := x

/--
error: unknown identifier 'x'
---
error: ❌️ Docstring on `#guard_msgs` does not match generated message:

error: unknown identifier 'x'
-/
#guard_msgs in
#guard_msgs in
example : α := x

#guard_msgs in
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : α := sorry

#guard_msgs in
/-- warning: declaration uses 'sorry' -/
#guard_msgs(warning) in
example : α := sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
#guard_msgs(error) in
example : α := sorry

#guard_msgs in
#guard_msgs(drop warning) in
example : α := sorry

#guard_msgs in
#guard_msgs(error, drop warning) in
example : α := sorry

#guard_msgs in
/-- error: unknown identifier 'x' -/
#guard_msgs(error, drop warning) in
example : α := x

#guard_msgs in
/--
error: failed to synthesize
  OfNat α 22
numerals are polymorphic in Lean, but the numeral `22` cannot be used in a context where the expected type is
  α
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs(error) in
example : α := 22

-- Trailing whitespace

/--
info: foo ⏎
bar
---
error: ❌️ Docstring on `#guard_msgs` does not match generated message:

info: foo ⏎
bar
-/
#guard_msgs in
#guard_msgs in
run_meta Lean.logInfo "foo \nbar"

#guard_msgs in
/--
info: foo ⏎
bar
-/
#guard_msgs in
run_meta Lean.logInfo "foo \nbar"

/--
info: foo ⏎⏎
bar
---
error: ❌️ Docstring on `#guard_msgs` does not match generated message:

info: foo ⏎⏎
bar
-/
#guard_msgs in
#guard_msgs in
run_meta Lean.logInfo "foo ⏎\nbar"

#guard_msgs in
/--
info: foo ⏎⏎
bar
-/
#guard_msgs in
run_meta Lean.logInfo "foo ⏎\nbar"

/-!
Lax whitespace
-/

/--
error: failed to synthesize
  DecidableEq (Nat → Nat)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in
#synth DecidableEq (Nat → Nat)

/--
error: failed to synthesize
  DecidableEq (Nat → Nat)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in
#synth DecidableEq (Nat → Nat)

/-!
Sorting
-/

/--
info: A
---
info: B
-/
#guard_msgs (ordering := sorted) in
run_meta do Lean.logInfo "B"; Lean.logInfo "A"

/--
info: B
---
info: A
-/
#guard_msgs in
run_meta do Lean.logInfo "B"; Lean.logInfo "A"

/-!
Linter suppression. `#guard_msgs` is special-cased by the command elaborator so that linters aren't
run on `#guard_msgs` itself, just on its command.
-/

set_option linter.unusedVariables true

#guard_msgs in
/--
warning: unused variable `n`
note: this linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
example (n : Nat) : True := trivial

#guard_msgs in
/--
warning: unused variable `n`
note: this linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
#guard_msgs (info) in
example (n : Nat) : True := trivial

/-!
Test diffs
-/

/--
info: ABCDEFG
HIJKLMNOP
QRSTUVWXYZ
---
error: ❌️ Docstring on `#guard_msgs` does not match generated message:

-
+ info: ABCDEFG
+ HIJKLMNOP
+ QRSTUVWXYZ
-/
#guard_msgs in
set_option guard_msgs.diff true in
#guard_msgs in
#eval IO.println "ABCDEFG\nHIJKLMNOP\nQRSTUVWXYZ"

/--
info: ABCDEFG
HIJKLMNOP
QRSTUVWXYZ
---
error: ❌️ Docstring on `#guard_msgs` does not match generated message:

  info: ABCDEFG
+ HIJKLMNOP
  QRSTUVWXYZ
-/
#guard_msgs in
set_option guard_msgs.diff true in
/--
info: ABCDEFG
QRSTUVWXYZ
-/
#guard_msgs in
#eval IO.println "ABCDEFG\nHIJKLMNOP\nQRSTUVWXYZ"

inductive Tree where
  | leaf (x : Nat)
  | branch (left : Tree) (x : Nat) (right : Tree)
deriving Repr

def Tree.build (n k : Nat) : Tree :=
  if n = 0 then leaf k else branch (Tree.build (n - 1) k) n (Tree.build (n - k - 1) (k / 2))

/--
info: Tree.branch
  (Tree.branch
    (Tree.branch
      (Tree.branch
        (Tree.branch
          (Tree.branch (Tree.branch (Tree.branch (Tree.leaf 3) 1 (Tree.leaf 1)) 2 (Tree.leaf 1)) 3 (Tree.leaf 1))
          4
          (Tree.leaf 1))
        5
        (Tree.branch (Tree.leaf 1) 1 (Tree.leaf 0)))
      6
      (Tree.branch (Tree.branch (Tree.leaf 1) 1 (Tree.leaf 0)) 2 (Tree.leaf 0)))
    7
    (Tree.branch
      (Tree.branch (Tree.branch (Tree.leaf 1) 1 (Tree.leaf 0)) 2 (Tree.leaf 0))
      3
      (Tree.branch (Tree.leaf 0) 1 (Tree.leaf 0))))
  8
  (Tree.branch
    (Tree.branch
      (Tree.branch (Tree.branch (Tree.leaf 1) 1 (Tree.leaf 0)) 2 (Tree.leaf 0))
      3
      (Tree.branch (Tree.leaf 0) 1 (Tree.leaf 0)))
    4
    (Tree.branch (Tree.branch (Tree.leaf 0) 1 (Tree.leaf 0)) 2 (Tree.branch (Tree.leaf 0) 1 (Tree.leaf 0))))
---
error: ❌️ Docstring on `#guard_msgs` does not match generated message:

  info: Tree.branch
    (Tree.branch
      (Tree.branch
        (Tree.branch
          (Tree.branch
-           (Tree.branch (Tree.branch (Tree.branch (Tree.leaf) 1 (Tree.leaf)) 2 (Tree.leaf)) 3 (Tree.leaf))
+           (Tree.branch (Tree.branch (Tree.branch (Tree.leaf 3) 1 (Tree.leaf 1)) 2 (Tree.leaf 1)) 3 (Tree.leaf 1))
            4
-           (Tree.leaf))
+           (Tree.leaf 1))
          5
-         (Tree.branch (Tree.leaf) 1 (Tree.leaf)))
+         (Tree.branch (Tree.leaf 1) 1 (Tree.leaf 0)))
        6
-       (Tree.branch (Tree.branch (Tree.leaf) 1 (Tree.leaf)) 2 (Tree.leaf)))
+       (Tree.branch (Tree.branch (Tree.leaf 1) 1 (Tree.leaf 0)) 2 (Tree.leaf 0)))
      7
      (Tree.branch
-       (Tree.branch (Tree.branch (Tree.leaf) 1 (Tree.leaf)) 2 (Tree.leaf))
+       (Tree.branch (Tree.branch (Tree.leaf 1) 1 (Tree.leaf 0)) 2 (Tree.leaf 0))
        3
-       (Tree.branch (Tree.leaf) 1 (Tree.leaf))))
+       (Tree.branch (Tree.leaf 0) 1 (Tree.leaf 0))))
    8
    (Tree.branch
      (Tree.branch
-       (Tree.branch (Tree.branch (Tree.leaf) 1 (Tree.leaf)) 2 (Tree.leaf))
+       (Tree.branch (Tree.branch (Tree.leaf 1) 1 (Tree.leaf 0)) 2 (Tree.leaf 0))
        3
-       (Tree.branch (Tree.leaf) 1 (Tree.leaf)))
+       (Tree.branch (Tree.leaf 0) 1 (Tree.leaf 0)))
      4
-     (Tree.branch (Tree.branch (Tree.leaf) 1 (Tree.leaf)) 2 (Tree.branch (Tree.leaf) 1 (Tree.leaf))))
+     (Tree.branch (Tree.branch (Tree.leaf 0) 1 (Tree.leaf 0)) 2 (Tree.branch (Tree.leaf 0) 1 (Tree.leaf 0))))
-/
#guard_msgs in
set_option guard_msgs.diff true in
/--
info: Tree.branch
  (Tree.branch
    (Tree.branch
      (Tree.branch
        (Tree.branch
          (Tree.branch (Tree.branch (Tree.branch (Tree.leaf) 1 (Tree.leaf)) 2 (Tree.leaf)) 3 (Tree.leaf))
          4
          (Tree.leaf))
        5
        (Tree.branch (Tree.leaf) 1 (Tree.leaf)))
      6
      (Tree.branch (Tree.branch (Tree.leaf) 1 (Tree.leaf)) 2 (Tree.leaf)))
    7
    (Tree.branch
      (Tree.branch (Tree.branch (Tree.leaf) 1 (Tree.leaf)) 2 (Tree.leaf))
      3
      (Tree.branch (Tree.leaf) 1 (Tree.leaf))))
  8
  (Tree.branch
    (Tree.branch
      (Tree.branch (Tree.branch (Tree.leaf) 1 (Tree.leaf)) 2 (Tree.leaf))
      3
      (Tree.branch (Tree.leaf) 1 (Tree.leaf)))
    4
    (Tree.branch (Tree.branch (Tree.leaf) 1 (Tree.leaf)) 2 (Tree.branch (Tree.leaf) 1 (Tree.leaf))))
-/
#guard_msgs in
#eval Tree.build 8 3
