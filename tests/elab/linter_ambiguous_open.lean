/-!
Tests for the `linter.ambiguousOpen` linter, which warns when the namespace of an `open`
declaration could also refer to a namespace that the `open` silently does not open, e.g.
`open B` inside `namespace A` when both `B` and `A.B` exist, which opens only `A.B`.
-/

-- The test suite runs with `linter.all=false`, so enable the (default-on) linter explicitly.
set_option linter.ambiguousOpen true

namespace A.B
def x := 1
def z := 2
end A.B

namespace B
def y := 3
def z := 4
end B

/-! An unambiguous `open` does not warn, even though `A.B` exists (`A` is not opened). -/

section
#guard_msgs in
open B
end

/-!
`open A` followed by `open B` opens both `_root_.B` and `A.B`; since no interpretation is
silently skipped, the linter does not warn.
-/

section
open A
#guard_msgs in
open B
-- Both namespaces are indeed opened:
#guard x == 1
#guard y == 3
end

section
#guard_msgs in
open A B
end

/-! Inside `namespace A`, `open B` silently refers to `A.B` only, shadowing `_root_.B`. -/

namespace A
/--
warning: Ambiguous namespace `B`: it is interpreted as `_root_.A.B` because this `open` occurs inside `namespace A`, while `_root_.B` is silently not opened. Specify the namespace unambiguously, e.g. `_root_.A.B`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`.

Note: This linter can be disabled with `set_option linter.ambiguousOpen false`
-/
#guard_msgs in
open B
-- Only `A.B` is opened:
#guard x == 1
end A

/-!
If the shadowed namespace is already opened, its declarations are accessible anyway and the
linter does not warn.
-/

section
open B
namespace A
#guard_msgs in
open B
#guard x == 1
#guard y == 3
end A
end

/-!
If the shadowed namespace was opened with `hiding` exceptions, the hidden names remain
inaccessible, so the linter still warns.
-/

section
open B hiding y
namespace A
/--
warning: Ambiguous namespace `B`: it is interpreted as `_root_.A.B` because this `open` occurs inside `namespace A`, while `_root_.B` is silently not opened. Specify the namespace unambiguously, e.g. `_root_.A.B`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`.

Note: This linter can be disabled with `set_option linter.ambiguousOpen false`
-/
#guard_msgs in
open B
end A
end

/-!
Likewise, a shadowed namespace enclosing the current scope is accessible anyway and does not
cause a warning.
-/

namespace B.C.B
def v := 6
end B.C.B

namespace B.C
#guard_msgs in
open B
-- `B.C.B` is opened, and the enclosing `_root_.B` is accessible without `open`:
#guard v == 6
#guard y == 3
end B.C

/-!
A single `open` can refer to several namespaces and still shadow another one; all silently
skipped interpretations are reported.
-/

namespace C.B
def u := 7
end C.B

namespace A
open C
/--
warning: Ambiguous namespace `B`: this `open` refers to all of `_root_.A.B`, `_root_.C.B`, while `_root_.B` is silently not opened because the `open` occurs inside `namespace A`. Specify the namespace unambiguously, e.g. `_root_.A.B`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`.

Note: This linter can be disabled with `set_option linter.ambiguousOpen false`
-/
#guard_msgs in
open B
#guard x == 1
#guard u == 7
end A

/-! Disambiguated forms do not warn. -/

namespace A
#guard_msgs in
open _root_.B
#guard_msgs in
open A.B
end A

/-! The linter can be disabled. -/

namespace A
set_option linter.ambiguousOpen false in
#guard_msgs in
open B
end A

/-! Other `open` variants are also linted. -/

namespace A
/--
warning: Ambiguous namespace `B`: it is interpreted as `_root_.A.B` because this `open` occurs inside `namespace A`, while `_root_.B` is silently not opened. Specify the namespace unambiguously, e.g. `_root_.A.B`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`.

Note: This linter can be disabled with `set_option linter.ambiguousOpen false`
-/
#guard_msgs in
open B (x)

/--
warning: Ambiguous namespace `B`: it is interpreted as `_root_.A.B` because this `open` occurs inside `namespace A`, while `_root_.B` is silently not opened. Specify the namespace unambiguously, e.g. `_root_.A.B`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`.

Note: This linter can be disabled with `set_option linter.ambiguousOpen false`
-/
#guard_msgs in
open B hiding x

/--
warning: Ambiguous namespace `B`: it is interpreted as `_root_.A.B` because this `open` occurs inside `namespace A`, while `_root_.B` is silently not opened. Specify the namespace unambiguously, e.g. `_root_.A.B`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`.

Note: This linter can be disabled with `set_option linter.ambiguousOpen false`
-/
#guard_msgs in
open B renaming x -> x'

/--
warning: Ambiguous namespace `B`: it is interpreted as `_root_.A.B` because this `open` occurs inside `namespace A`, while `_root_.B` is silently not opened. Specify the namespace unambiguously, e.g. `_root_.A.B`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`.

Note: This linter can be disabled with `set_option linter.ambiguousOpen false`
-/
#guard_msgs in
open scoped B
end A

/-! `open ... in` at the term level is also linted. -/

namespace A
/--
warning: Ambiguous namespace `B`: it is interpreted as `_root_.A.B` because this `open` occurs inside `namespace A`, while `_root_.B` is silently not opened. Specify the namespace unambiguously, e.g. `_root_.A.B`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`.

Note: This linter can be disabled with `set_option linter.ambiguousOpen false`
-/
#guard_msgs in
example : Nat := open B in x
end A

/-!
Macro-generated `open` declarations (whose identifiers carry no original source info) are not
linted, since the warning could not be addressed at the use site.
-/

namespace A
macro "open_b_via_macro" : command => `(open $(Lean.mkIdent `B):ident)
#guard_msgs in
open_b_via_macro
-- The macro-generated `open` still takes effect, opening `A.B`:
#guard x == 1
end A

/-! Deeper shadowing: inside `namespace A.C`, candidates from several scope prefixes. -/

namespace A.C.B
def w := 5
end A.C.B

namespace A.C
/--
warning: Ambiguous namespace `B`: it is interpreted as `_root_.A.C.B` because this `open` occurs inside `namespace A.C`, while `_root_.A.B`, `_root_.B` are silently not opened. Specify the namespace unambiguously, e.g. `_root_.A.C.B`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`.

Note: This linter can be disabled with `set_option linter.ambiguousOpen false`
-/
#guard_msgs in
open B
#guard w == 5
end A.C
