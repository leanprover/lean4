import Lean.Server.FileWorker.SemanticHighlighting

open Lean Server.FileWorker

deriving instance Repr for Lsp.SemanticTokenType
deriving instance Repr for AbsoluteLspSemanticToken

/-!
# Non-Overlapping Cases

When no tokens overlap, and they are all sorted, then `handleOverlappingSemanticTokens` is the
identity.
-/

def noOverlaps : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 5⟩
    tailPos := ⟨1, 7⟩
    type := .keyword },
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .function },
  { pos := ⟨1, 10⟩
    tailPos := ⟨1, 14⟩
    type := .keyword }
]

#guard handleOverlappingSemanticTokens noOverlaps == noOverlaps

/-!
When no tokens overlap, then `handleOverlappingSemanticTokens` is equivalent to sorting the tokens
by their start position.
-/

partial def permutations (xs : Array α) :=
  if h : xs.size > 0 then
    go h ⟨xs.size, by grind⟩ xs.toVector |>.run #[] |>.2
  else #[]
where
  go (h : xs.size > 0) (k : Fin (xs.size + 1)) (ys : Vector α xs.size) : StateM (Array (Array α)) Unit := do
    if h0 : k = 0 then pure ()
    else if h1 : k = 1 then
      modify (·.push ys.toArray)
    else
      go h (k - 1) ys
      for h' : i in [0 : k - 1] do
        have : i < xs.size := by
          cases h'
          grind
        go h (k - 1) <|
          if k % 2 == 0 then
            ys.swapIfInBounds i (k - 1)
          else
            ys.swapIfInBounds 0 (k - 1)

#guard (permutations noOverlaps).map handleOverlappingSemanticTokens |>.all (· == noOverlaps)

/-!
# Duplicate and Co-Extensive Tokens

Duplicate tokens are removed
-/

def duplicate : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 5⟩
    tailPos := ⟨1, 7⟩
    type := .keyword },
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .function },
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .function },
  { pos := ⟨1, 10⟩
    tailPos := ⟨1, 14⟩
    type := .keyword }
]

#guard handleOverlappingSemanticTokens duplicate == noOverlaps

/-!
When two tokens are co-extensive, the highest priority is retained.
If the priorities are the same, then the later token is retained.
-/
def sameRange1 : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 5⟩
    tailPos := ⟨1, 7⟩
    type := .keyword },
  -- Here, we have two tokens in the same range with the same priority:
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .function },
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .variable },
  { pos := ⟨1, 10⟩
    tailPos := ⟨1, 14⟩
    type := .keyword }
]

def sameRange1expected : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 5⟩
    tailPos := ⟨1, 7⟩
    type := .keyword },
  -- The later of the two coextensive tokens (WRT the input array) is retained.
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .variable },
  { pos := ⟨1, 10⟩
    tailPos := ⟨1, 14⟩
    type := .keyword }
]

#guard handleOverlappingSemanticTokens sameRange1 == sameRange1expected

def sameRange1' : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 5⟩
    tailPos := ⟨1, 7⟩
    type := .keyword },
  -- Here, we have two tokens in the same range with the same priority:
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .variable },
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .function },
  { pos := ⟨1, 10⟩
    tailPos := ⟨1, 14⟩
    type := .keyword }
]

def sameRange1'expected : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 5⟩
    tailPos := ⟨1, 7⟩
    type := .keyword },
  -- The later of the two coextensive tokens (WRT the input array) is retained.
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .function },
  { pos := ⟨1, 10⟩
    tailPos := ⟨1, 14⟩
    type := .keyword }
]
#guard handleOverlappingSemanticTokens sameRange1' == sameRange1'expected

def sameRange2 : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 5⟩
    tailPos := ⟨1, 7⟩
    type := .keyword },
  -- Here, we have two tokens in the same range with different priorities.
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .function },
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .variable
    priority := 6 },
  { pos := ⟨1, 10⟩
    tailPos := ⟨1, 14⟩
    type := .keyword }
]

def sameRange2expected : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 5⟩
    tailPos := ⟨1, 7⟩
    type := .keyword },
  -- The higher-priority token is retained.
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .variable
    priority := 6 },
  { pos := ⟨1, 10⟩
    tailPos := ⟨1, 14⟩
    type := .keyword }
]

#guard handleOverlappingSemanticTokens sameRange2 == sameRange2expected


def sameRange3 : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 5⟩
    tailPos := ⟨1, 7⟩
    type := .keyword },
  -- Here, we have two tokens in the same range with different priorities.
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .function
    priority := 6 },
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .variable },
  { pos := ⟨1, 10⟩
    tailPos := ⟨1, 14⟩
    type := .keyword }
]

def sameRange3expected : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 5⟩
    tailPos := ⟨1, 7⟩
    type := .keyword },
  -- The higher-priority token is retained.
  { pos := ⟨1, 8⟩
    tailPos := ⟨1, 10⟩
    type := .function
    priority := 6 },
  { pos := ⟨1, 10⟩
    tailPos := ⟨1, 14⟩
    type := .keyword }
]

#guard handleOverlappingSemanticTokens sameRange3 == sameRange3expected

/-!
# General Overlaps

This is the following situation:

Given tokens A, B, C, D as in:
```
|-----A------|  |----D----|
    |------B----------|
        |----C----|
```
with priorities C > B, B > A, B > D, we want to emit the tokens:
```
|-A-|-B-|----C----|-B-|-D--|
```
In other words, `B` is split into two regions: before and after `C`.

-/

def multiOverlap : Array AbsoluteLspSemanticToken := #[
  -- A
  { pos := ⟨1, 1⟩
    tailPos := ⟨1, 14⟩
    type := .function
    priority := 3 },
  -- B
  { pos := ⟨1, 5⟩
    tailPos := ⟨1, 23⟩
    type := .string
    priority := 4 },
  -- C
  { pos := ⟨1, 9⟩
    tailPos := ⟨1, 19⟩
    type := .property
    priority := 5 },
  -- D
  { pos := ⟨1, 17⟩
    tailPos := ⟨1, 27⟩
    type := .keyword
    priority := 3 },
]

def multiExpected : Array AbsoluteLspSemanticToken := #[
  -- A
  { pos := { line := 1, character := 1 },
    tailPos := { line := 1, character := 5 },
    type := .function
    priority := 3 },
  -- B
  { pos := { line := 1, character := 5 },
    tailPos := { line := 1, character := 9 },
    type := .string
    priority := 4 },
  -- C
  { pos := { line := 1, character := 9 },
    tailPos := { line := 1, character := 19 },
    type := .property
    priority := 5 },
  -- B
  { pos := { line := 1, character := 19 },
    tailPos := { line := 1, character := 23 },
    type := .string
    priority := 4 },
  -- D
  { pos := { line := 1, character := 23 },
    tailPos := { line := 1, character := 27 },
    type := .keyword
    priority := 3 }]

#guard handleOverlappingSemanticTokens multiOverlap == multiExpected

def overlappingLeftRight : Array AbsoluteLspSemanticToken := #[
  -- An overlap of left over right
  { pos := ⟨2, 5⟩
    tailPos := ⟨2, 10⟩
    type := .function
    priority := 6 },
  { pos := ⟨2, 7⟩
    tailPos := ⟨2, 13⟩
    type := .function
    priority := 5 },
  -- An overlap of right over left
  { pos := ⟨3, 5⟩
    tailPos := ⟨3, 10⟩
    type := .function
    priority := 4 },
  { pos := ⟨3, 7⟩
    tailPos := ⟨3, 13⟩
    type := .function
    priority := 5 },
]

def overlappingLeftRightExpected : Array AbsoluteLspSemanticToken := #[
  -- Left over right:
  { pos := ⟨2, 5⟩
    tailPos := ⟨2, 10⟩
    type := .function
    priority := 6 },
  { pos := ⟨2, 10⟩
    tailPos := ⟨2, 13⟩
    type := .function
    priority := 5 },
  -- Right over left:
  { pos := ⟨3, 5⟩
    tailPos := ⟨3, 7⟩
    type := .function
    priority := 4 },
  { pos := ⟨3, 7⟩
    tailPos := ⟨3, 13⟩
    type := .function
    priority := 5 },
]

#guard handleOverlappingSemanticTokens overlappingLeftRight == overlappingLeftRightExpected

/-!
If two tokens start at the same position and have the same priority, the shorter one is used first.
-/

def sameStart : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 3⟩
    tailPos := ⟨1, 5⟩
    type := .function },
  { pos := ⟨1, 3⟩
    tailPos := ⟨1, 8⟩
    type := .string },
]

def sameStartExpected : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 3⟩
    tailPos := ⟨1, 5⟩
    type := .function },
  { pos := ⟨1, 5⟩
    tailPos := ⟨1, 8⟩
    type := .string },

]

#guard handleOverlappingSemanticTokens sameStart == sameStartExpected

def sameStart' : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 3⟩
    tailPos := ⟨1, 8⟩
    type := .string },
  { pos := ⟨1, 3⟩
    tailPos := ⟨1, 5⟩
    type := .function },
]

#guard handleOverlappingSemanticTokens sameStart' == sameStartExpected

/-!
If two tokens end at the same position, then the shorter one takes precedence over the longer one in
its range.
-/

def sameEnd : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 1⟩
    tailPos := ⟨1, 5⟩
    type := .function },
  { pos := ⟨1, 3⟩
    tailPos := ⟨1, 5⟩
    type := .string },
]

def sameEndExpected : Array AbsoluteLspSemanticToken := #[
  { pos := { line := 1, character := 1 },
    tailPos := { line := 1, character := 3 },
    type := Lean.Lsp.SemanticTokenType.function,
    priority := 5 },
  { pos := { line := 1, character := 3 },
    tailPos := { line := 1, character := 5 },
    type := Lean.Lsp.SemanticTokenType.string,
    priority := 5 }]

#guard handleOverlappingSemanticTokens sameEnd == sameEndExpected
#guard handleOverlappingSemanticTokens sameEnd.reverse == sameEndExpected

def overlapMiddle : Array AbsoluteLspSemanticToken := #[
  { pos := ⟨1, 1⟩
    tailPos := ⟨1, 5⟩
    type := .function },
  { pos := ⟨1, 3⟩
    tailPos := ⟨1, 8⟩
    type := .string },
]

def overlapMiddleExpected : Array AbsoluteLspSemanticToken := #[
  { pos := { line := 1, character := 1 },
    tailPos := { line := 1, character := 3 },
    type := Lean.Lsp.SemanticTokenType.function,
    priority := 5 },
  { pos := { line := 1, character := 3 },
    tailPos := { line := 1, character := 8 },
    type := Lean.Lsp.SemanticTokenType.string,
    priority := 5 }
]

#guard handleOverlappingSemanticTokens overlapMiddle == overlapMiddleExpected
#guard handleOverlappingSemanticTokens overlapMiddle.reverse == overlapMiddleExpected
