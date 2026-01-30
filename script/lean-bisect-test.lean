/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

namespace Strata
namespace Python

/-
Parser and translator for some basic regular expression patterns supported by
Python's `re` library
Ref.: https://docs.python.org/3/library/re.html

Also see
https://github.com/python/cpython/blob/759a048d4bea522fda2fe929be0fba1650c62b0e/Lib/re/_parser.py
for a reference implementation.
-/

-------------------------------------------------------------------------------

inductive ParseError where
  /--
    `patternError` is raised when Python's `re.patternError` exception is
    raised.
    [Reference: Python's re exceptions](https://docs.python.org/3/library/re.html#exceptions):

    "Exception raised when a string passed to one of the functions here is not a
    valid regular expression (for example, it might contain unmatched
    parentheses) or when some other error occurs during compilation or matching.
    It is never an error if a string contains no match for a pattern."
  -/
  | patternError  (message : String) (pattern : String) (pos : String.Pos.Raw)
  /--
  `unimplemented` is raised whenever we don't support some regex operations
  (e.g., lookahead assertions).
  -/
  | unimplemented (message : String) (pattern : String) (pos : String.Pos.Raw)
  deriving Repr

def ParseError.toString : ParseError → String
  | .patternError msg pat pos => s!"Pattern error at position {pos.byteIdx}: {msg} in pattern '{pat}'"
  | .unimplemented msg pat pos => s!"Unimplemented at position {pos.byteIdx}: {msg} in pattern '{pat}'"

instance : ToString ParseError where
  toString := ParseError.toString

-------------------------------------------------------------------------------

/--
Regular Expression Nodes
-/
inductive RegexAST where
  /-- Single literal character: `a` -/
  | char : Char → RegexAST
  /-- Character range: `[a-z]` -/
  | range : Char → Char → RegexAST
  /-- Alternation: `a|b` -/
  | union : RegexAST → RegexAST → RegexAST
  /-- Concatenation: `ab` -/
  | concat : RegexAST → RegexAST → RegexAST
  /-- Any character: `.` -/
  | anychar : RegexAST
  /-- Zero or more: `a*` -/
  | star : RegexAST → RegexAST
  /-- One or more: `a+` -/
  | plus : RegexAST → RegexAST
  /-- Zero or one: `a?` -/
  | optional : RegexAST → RegexAST
  /-- Bounded repetition: `a{n,m}` -/
  | loop : RegexAST → Nat → Nat → RegexAST
  /-- Start of string: `^` -/
  | anchor_start : RegexAST
  /-- End of string: `$` -/
  | anchor_end : RegexAST
  /-- Grouping: `(abc)` -/
  | group : RegexAST → RegexAST
  /-- Empty string: `()` or `""` -/
  | empty : RegexAST
  /-- Complement: `[^a-z]` -/
  | complement : RegexAST → RegexAST
  deriving Inhabited, Repr

-------------------------------------------------------------------------------

/-- Parse character class like [a-z], [0-9], etc. into union of ranges and
  chars. Note that this parses `|` as a character. -/
def parseCharClass (s : String) (pos : String.Pos.Raw) : Except ParseError (RegexAST × String.Pos.Raw) := do
  if pos.get? s != some '[' then throw (.patternError "Expected '[' at start of character class" s pos)
  let mut i := pos.next s

  -- Check for complement (negation) with leading ^
  let isComplement := !i.atEnd s && i.get? s == some '^'
  if isComplement then
    i := i.next s

  let mut result : Option RegexAST := none

  -- Process each element in the character class.
  while !i.atEnd s && i.get? s != some ']' do
    -- Uncommenting this makes the code stop
    --dbg_trace "Working" (pure ())
    let some c1 := i.get? s | throw (.patternError "Invalid character in class" s i)
    let i1 := i.next s
    -- Check for range pattern: c1-c2.
    if !i1.atEnd s && i1.get? s == some '-' then
      let i2 := i1.next s
      if !i2.atEnd s && i2.get? s != some ']' then
        let some c2 := i2.get? s | throw (.patternError "Invalid character in range" s i2)
        if c1 > c2 then
          throw (.patternError s!"Invalid character range [{c1}-{c2}]: \
                                  start character '{c1}' is greater than end character '{c2}'" s i)
        let r := RegexAST.range c1 c2
        -- Union with previous elements.
        result := some (match result with | none => r | some prev => RegexAST.union prev r)
        i := i2.next s
        continue
    -- Single character.
    let r := RegexAST.char c1
    result := some (match result with | none => r | some prev => RegexAST.union prev r)
    i := i.next s

  let some ast := result | throw (.patternError "Unterminated character set" s pos)
  let finalAst := if isComplement then RegexAST.complement ast else ast
  pure (finalAst, i.next s)

-------------------------------------------------------------------------------

/-- Parse numeric repeats like `{10}` or `{1,10}` into min and max bounds. -/
def parseBounds (s : String) (pos : String.Pos.Raw) : Except ParseError (Nat × Nat × String.Pos.Raw) := do
  if pos.get? s != some '{' then throw (.patternError "Expected '{' at start of bounds" s pos)
  let mut i := pos.next s
  let mut numStr := ""

  -- Parse first number.
  while !i.atEnd s && (i.get? s).any Char.isDigit do
    numStr := numStr.push ((i.get? s).get!)
    i := i.next s

  let some n := numStr.toNat? | throw (.patternError "Invalid minimum bound" s pos)

  -- Check for comma (range) or closing brace (exact count).
  match i.get? s with
  | some '}' => pure (n, n, i.next s)  -- {n} means exactly n times.
  | some ',' =>
    i := i.next s
    -- Parse maximum bound
    numStr := ""
    while !i.atEnd s && (i.get? s).any Char.isDigit do
      numStr := numStr.push ((i.get? s).get!)
      i := i.next s
    let some max := numStr.toNat? | throw (.patternError "Invalid maximum bound" s i)
    if i.get? s != some '}' then throw (.patternError "Expected '}' at end of bounds" s i)
    -- Validate bounds order
    if max < n then
      throw (.patternError s!"Invalid repeat bounds \{{n},{max}}: \
                              maximum {max} is less than minimum {n}" s pos)
    pure (n, max, i.next s)
  | _ => throw (.patternError "Invalid bounds syntax" s i)

-------------------------------------------------------------------------------

mutual
/--
Parse atom: single element (char, class, anchor, group) with optional
quantifier. Stops at the first `|`.
-/
partial def parseAtom (s : String) (pos : String.Pos.Raw) : Except ParseError (RegexAST × String.Pos.Raw) := do
  if pos.atEnd s then throw (.patternError "Unexpected end of regex" s pos)

  let some c := pos.get? s | throw (.patternError "Invalid position" s pos)

  -- Detect invalid quantifier at start
  if c == '*' || c == '+' || c == '{' || c == '?' then
    throw (.patternError s!"Quantifier '{c}' at position {pos} has nothing to quantify" s pos)

  -- Detect unbalanced closing parenthesis
  if c == ')' then
    throw (.patternError "Unbalanced parenthesis" s pos)

  -- Parse base element (anchor, char class, group, anychar, escape, or single char).
  let (base, nextPos) ← match c with
    | '^' => pure (RegexAST.anchor_start, pos.next s)
    | '$' => pure (RegexAST.anchor_end, pos.next s)
    | '[' => parseCharClass s pos
    | '(' => parseExplicitGroup s pos
    | '.' => pure (RegexAST.anychar, pos.next s)
    | '\\' =>
      -- Handle escape sequence.
      -- Note: Python uses a single backslash as an escape character, but Lean
      -- strings need to escape that. After DDMification, we will see two
      -- backslashes in Strata for every Python backslash.
      let nextPos := pos.next s
      if nextPos.atEnd s then throw (.patternError "Incomplete escape sequence at end of regex" s pos)
      let some escapedChar := nextPos.get? s | throw (.patternError "Invalid escape position" s nextPos)
      -- Check for special sequences (unsupported right now).
      match escapedChar with
      | 'A' | 'b' | 'B' | 'd' | 'D' | 's' | 'S' | 'w' | 'W' | 'z' | 'Z' =>
        throw (.unimplemented s!"Special sequence \\{escapedChar} is not supported" s pos)
      | 'a' | 'f' | 'n' | 'N' | 'r' | 't' | 'u' | 'U' | 'v' | 'x' =>
        throw (.unimplemented s!"Escape sequence \\{escapedChar} is not supported" s pos)
      | c =>
        if c.isDigit then
          throw (.unimplemented s!"Backreference \\{c} is not supported" s pos)
        else
          pure (RegexAST.char escapedChar, nextPos.next s)
    | _ => pure (RegexAST.char c, pos.next s)

  -- Check for numeric repeat suffix on base element (but not on anchors)
  match base with
  | .anchor_start | .anchor_end => pure (base, nextPos)
  | _ =>
    if !nextPos.atEnd s then
      match nextPos.get? s with
      | some '{' =>
        let (min, max, finalPos) ← parseBounds s nextPos
        pure (RegexAST.loop base min max, finalPos)
      | some '*' =>
        let afterStar := nextPos.next s
        if !afterStar.atEnd s then
          match afterStar.get? s with
          | some '?' => throw (.unimplemented "Non-greedy quantifier *? is not supported" s nextPos)
          | some '+' => throw (.unimplemented "Possessive quantifier *+ is not supported" s nextPos)
          | _ => pure (RegexAST.star base, afterStar)
        else pure (RegexAST.star base, afterStar)
      | some '+' =>
        let afterPlus := nextPos.next s
        if !afterPlus.atEnd s then
          match afterPlus.get? s with
          | some '?' => throw (.unimplemented "Non-greedy quantifier +? is not supported" s nextPos)
          | some '+' => throw (.unimplemented "Possessive quantifier ++ is not supported" s nextPos)
          | _ => pure (RegexAST.plus base, afterPlus)
        else pure (RegexAST.plus base, afterPlus)
      | some '?' =>
        let afterQuestion := nextPos.next s
        if !afterQuestion.atEnd s then
          match afterQuestion.get? s with
          | some '?' => throw (.unimplemented "Non-greedy quantifier ?? is not supported" s nextPos)
          | some '+' => throw (.unimplemented "Possessive quantifier ?+ is not supported" s nextPos)
          | _ => pure (RegexAST.optional base, afterQuestion)
        else pure (RegexAST.optional base, afterQuestion)
      | _ => pure (base, nextPos)
    else
      pure (base, nextPos)

/-- Parse explicit group with parentheses. -/
partial def parseExplicitGroup (s : String) (pos : String.Pos.Raw) : Except ParseError (RegexAST × String.Pos.Raw) := do
  if pos.get? s != some '(' then throw (.patternError "Expected '(' at start of group" s pos)
  let mut i := pos.next s

  -- Check for extension notation (?...
  if !i.atEnd s && i.get? s == some '?' then
    let i1 := i.next s
    if !i1.atEnd s then
      match i1.get? s with
      | some '=' => throw (.unimplemented "Positive lookahead (?=...) is not supported" s pos)
      | some '!' => throw (.unimplemented "Negative lookahead (?!...) is not supported" s pos)
      | _ => throw (.unimplemented "Extension notation (?...) is not supported" s pos)

  let (inner, finalPos) ← parseGroup s i (some ')')
  pure (.group inner, finalPos)

/-- Parse group: handles alternation and concatenation at current scope. -/
partial def parseGroup (s : String) (pos : String.Pos.Raw) (endChar : Option Char) :
    Except ParseError (RegexAST × String.Pos.Raw) := do
  let mut alternatives : List (List RegexAST) := [[]]
  let mut i := pos

  -- Parse until end of string or `endChar`.
  while !i.atEnd s && (endChar.isNone || i.get? s != endChar) do
    if i.get? s == some '|' then
      -- Push a new scope to `alternatives`.
      alternatives := [] :: alternatives
      i := i.next s
    else
      let (ast, nextPos) ← parseAtom s i
      alternatives := match alternatives with
        | [] => [[ast]]
        | head :: tail => (ast :: head) :: tail
      i := nextPos

  -- Check for expected end character.
  if let some ec := endChar then
    if i.get? s != some ec then
      throw (.patternError s!"Expected '{ec}'" s i)
    i := i.next s

  -- Build result: concatenate each alternative, then union them.
  let concatAlts := alternatives.reverse.filterMap fun alt =>
    match alt.reverse with
    | [] => -- Empty regex.
      some (.empty)
    | [single] => some single
    | head :: tail => some (tail.foldl RegexAST.concat head)

  match concatAlts with
  | [] => pure (.empty, i)
  | [single] => pure (single, i)
  | head :: tail => pure (tail.foldl RegexAST.union head, i)
end

/-- info: Except.ok (Strata.Python.RegexAST.range 'A' 'z', { byteIdx := 5 }) -/
#guard_msgs in
#eval parseCharClass "[A-z]" ⟨0⟩

-- Test code: Print done
#print "Done!"
