/-!
Tests that module doc comments are formatted like doc comments: the indentation of their text is
normalized, and the text keeps the indentation of its lines relative to each other.
-/

/-! # A module doc comment on one line -/

-- The text fits on the line of `/-!`.
/-!
# Title
-/

/-!   Text on the first line,
    with an indented second line.

    * A list item
      that continues on the next line.

    ```
    def f := 1
    ```
-/

namespace N
  /-!
    # Indented
    The indentation of the module doc comment is removed.
  -/
end N

/-! -/

/-! # A module doc comment with a comment after it -/ -- c

/-!
See https://example.com/xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx for details.
-/
def g := 1
