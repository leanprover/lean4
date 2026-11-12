import Lean

/-!
Tests that `syntax` declarations report deprecated parsers they refer to.
-/

set_option linter.deprecated true

open Lean Parser

def replacementParser : Parser := ident
@[deprecated replacementParser (since := "2025-01-01")] def deprecatedParser : Parser := ident

/--
warning: `deprecatedParser` has been deprecated: Use `replacementParser` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵P̵a̵r̵s̵e̵r̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲P̲a̲r̲s̲e̲r̲
-/
#guard_msgs in
syntax "useDeprecatedParser " deprecatedParser : term

/--
warning: `deprecatedParser` has been deprecated: Use `replacementParser` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵P̵a̵r̵s̵e̵r̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲P̲a̲r̲s̲e̲r̲
-/
#guard_msgs in
syntax "useDeprecatedParser? " (deprecatedParser)? : term

/--
warning: `deprecatedParser` has been deprecated: Use `replacementParser` instead

Hint: Replace the deprecated name:
  d̵e̵p̵r̵e̵c̵a̵t̵e̵d̵P̵a̵r̵s̵e̵r̵r̲e̲p̲l̲a̲c̲e̲m̲e̲n̲t̲P̲a̲r̲s̲e̲r̲
-/
#guard_msgs in
syntax "useDeprecatedParser,* " deprecatedParser,* : term

#guard_msgs in
syntax "useReplacementParser " replacementParser : term
