module

/-!
Tests for `fmtInterpolatedStr`, the formatter for interpolated string literals.
Interpolated strings are broken like ordinary string literals, with interpolations treated as
flattened word-like units; an interpolation is only broken apart according to its internal
formatting when even placing it on its own line overflows the line width.
-/

def name : String := "World"

def count : Nat := 42

def veryLongVariableNameForTesting : Nat := 1

def anotherRatherLongVariableName : Nat := 2

-- Short interpolated strings are left alone.
def hello : String := s!"Hello, {name}!"

def adjacent : String := s!"{name}{count}"

def atStart : String := s!"{count} items found"

def atEnd : String := s!"total: {count}"

-- Long interpolated strings are broken at word boundaries, with interpolations filling the lines
-- like words.
def longWithInterpolations : String :=
  s!"the value of the first counter is {count} and the name that was configured for it is {name}, \
    all good"

-- Interpolations glued to text are kept together with it; when the line overflows, the
-- interpolation may still be moved to its own line.
def gluedInterpolation : String :=
  s!"debug output: name={name},count={count},longName={veryLongVariableNameForTesting},another=\
    {anotherRatherLongVariableName}"

-- An interpolation that fits on a line by itself is placed on its own line, but kept intact.
def intactOnOwnLine : String :=
  s!"the sum of the two long variables is \
    {veryLongVariableNameForTesting + anotherRatherLongVariableName} as computed above"

-- An interpolation that does not fit on a line even by itself is broken apart according to its
-- internal formatting.
def brokenApart : String :=
  s!"the result of the computation is \
    {veryLongVariableNameForTesting + anotherRatherLongVariableName + veryLongVariableNameForTesting
      + anotherRatherLongVariableName + count} \
    and that concludes the analysis"

-- Newlines and escapes behave as in ordinary string literals.
def withNewlines : String :=
  s!"first line with {name}\
    \nsecond line with {count}"

def withEscapes : String :=
  s!"literal brace \{ and closing brace } and value {count} with a tab\tinside"

-- Trailing CRLF sequences are kept together with the content.
def contentLengthHeader (msg : String) : String :=
  s!"Content-Length: {toString msg.utf8ByteSize}\r\n\r\n"

-- Interpolations may contain nested strings.
def nestedString : String := s!"greeting: {String.intercalate ", " ["hello", "hi", "hey"]} end"

def messageData : IO Unit :=
  IO.println s!"processing item {count} of {count} with the configured name {name} and both long \
    variables set"
