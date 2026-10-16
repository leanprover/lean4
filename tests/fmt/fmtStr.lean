module

/-!
Tests for `fmtStr`, the formatter for non-interpolated string literals.
Long strings are broken at word boundaries by inserting string gaps (`\` at the end of a line);
newlines in the string are made explicit as `\n` at the start of the line they introduce, with a
string gap before them; newlines at the start and at the end of the string are kept with the
content; existing string gaps are retained.
-/

-- Short strings are left alone.
def greeting : String := "hello world"

def emptyString : String := ""

def whitespaceOnly : String := "   "

def endsWithSpaces : String := "some trailing spaces   "

def startsWithSpaces : String := "   some leading spaces"

-- A long string is broken at word boundaries, filling as many words as possible per line.
def loremIpsum : String :=
  "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut \
    labore et dolore magna aliqua."

-- A string that fits exactly is not broken.
def exactlyFits : String := "this string fits on a single line together with its declaration nicely"

-- A string that does not quite fit on one line together with its declaration is moved to its
-- own line as a whole instead of being split.
def justOverLimit : String :=
  "this string does not quite fit on a single line together with its declaration"

-- `\n` escapes between content lines always break the line, even when the string would fit on
-- one line, with the `\n` at the start of the line it introduces.
def twoLines : String :=
  "first line\
    \nsecond line"

def threeLines : String :=
  "a\
    \nb\
    \nc"

def emptyLines : String :=
  "paragraph one\
    \n\
    \nparagraph two"

-- Newlines at the start and at the end of the string do not separate two content lines and are
-- kept together with the content.
def endsWithNewline : String := "ends with a newline\n"

def startsWithNewline : String := "\nstarts with a newline"

def startsWithNewlineLong : String :=
  "\nstarts with a newline and is sufficiently long that it must nevertheless be broken at one of \
    its word boundaries"

def trailingNewlines : String := "\n\nExtensions:\n\n"

-- A run of leading newlines longer than the line is broken between the newlines.
def manyLeadingNewlines : String :=
  "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\
    \n\n\n\n\n\n\ncontent at the end"

-- A `\n` with spaces after it starts the next line, with the spaces serving as indentation.
def indentedContinuation : String :=
  "items:\
    \n  - first item of the list\
    \n  - second item of the list"

-- Literal newlines in multi-line string inputs are converted to explicit `\n` escapes;
-- these entries show the already-converted fixpoint.
def multiLine : String :=
  "this string\
    \nspans multiple\
    \nlines"

def multiLineIndented : String :=
  "structured:\
    \n  first indented line\
    \n  second indented line"

-- Existing string gaps are retained.
def alreadyFormatted : String :=
  "one \
    two \
    three"

-- A single word that does not fit on a line on its own is split with a string gap.
def url : String :=
  "https://very-long-url.example.com/with/lots/of/path/segments/and/query?params=true&more=yes&even\
    =more&stuff=here"

-- A long word that fits on a line by itself is not split; the line is broken before it instead.
def longWordAmongWords : String :=
  "see documentation at \
    https://lean-lang.org/doc/reference/latest/some/deeply/nested/section/anchor for details"

-- Escape sequences are kept intact and are never split.
def escapes : String :=
  "tab\there quote\"here backslash\\here hex\x41here unicode\u0041here carriage\rreturn"

def longEscapes : String :=
  "a very long string containing escapes such as \t and \\ and \" and \x41 and \u0041 that needs \
    to be broken"

-- Raw string literals are retained as-is.
def rawString : String :=
  r"raw strings \cannot \contain \string \gaps and are therefore never broken, no matter how long they are"

def rawMultiLine : String :=
  r#"raw strings
keep their literal
line structure"#

-- Long words with long whitespace runs: whitespace is never broken and never starts a line.
def wideWhitespace : String :=
  "columns:  first          second          third          fourth          fifth          \
    sixth          seventh"

-- Whitespace before a `\n` stays on the line before it.
def spacesBeforeNewline : String :=
  "a table row with much trailing padding                                   \
    \n  and its continuation line"

-- When the `\n` and the content after it do not fit on the next line together, the line is
-- broken again directly after the `\n`, so that the content gets the full next line for itself.
def newlineWithLongWord : String :=
  "prefix:\
    \n\
    path/to/some/deeply/nested/directory/structure/with/a/rather/long/single/component/dir/file.txt"

-- An escaped `\r` directly before a `\n` is kept together with it as a single CRLF newline,
-- including in the leading and trailing newline runs.
def httpResponse : String :=
  "HTTP/1.1 200 OK\
    \r\nContent-Type: text/html; charset=utf-8\
    \r\nCache-Control: no-cache\r\n\r\n"

-- Strings in nested positions are indented relative to their context.
structure DocumentedConfig where
  description : String :=
    "a quite long default description for this configuration field that will certainly not fit here"

def nestedInDo : IO Unit := do
  let mut message :=
    "an accumulated diagnostic message that is assembled from several long parts and does not fit"
  if message.length > 10 then
    message :=
      "another rather long replacement message that also does not fit on a single line at this \
        depth"
  IO.println message

def asArgument : IO Unit :=
  IO.println
    "a long string passed directly as an argument to a function call that will need to be broken"

def inList : List String := [
  "short",
  "a longer string in a list literal that together with its siblings exceeds the line length \
    limit",
  "tail"
]
