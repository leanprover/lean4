/-!
Tests for the placement of comments around tokens that span several lines (multi-line string
literals, in particular).
The fallback comment insertion mechanism, which inserts comments into the rendered output rather
than into the document, must never place a comment within such a token; comments that would be
placed there are moved to the line before the token instead.
-/

def f (a b : String) : String := a ++ b

def g (a : String) : String := a

-- A comment after a token that is followed by a multi-line token on the same rendered line.
def afterTokenBeforeMultiLineToken := f "x" -- comment
  "abc
def"

-- The same for a block comment.
def blockAfterTokenBeforeMultiLineToken := f "x" /- comment -/
  "abc
def"

-- A comment after a multi-line token can stay on the token's last line.
def afterMultiLineToken :=
  f "abc
def" -- comment
    "y"

-- Several multi-line tokens on the same line of the input.
def betweenMultiLineTokens :=
  f "abc
def" ("ghi
jkl") -- comment

-- A comment on its own line before a token that is rendered on a continuation line of a multi-line
-- token.
def beforeTokenOnContinuationLine := (g "abc
def"
  -- comment
  )

-- The same for a block comment.
def blockBeforeTokenOnContinuationLine := (g "abc
def"
  /- comment -/
  )

-- A comment group spanning several lines.
def multiLineCommentGroup := f "x" -- first
  -- second
  "abc
def"
