/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Lars König

The string fuzzy matching algorithm in this file is based on the algorithm
used in LLVM with some modifications. The LLVM algorithm itself is based on VS
code's client side filtering algorithm. For the LLVM implementation see
https://clang.llvm.org/extra//doxygen/FuzzyMatch_8cpp_source.html
-/
prelude
import Init.Data.Range
import Init.Data.OfScientific

namespace Lean
namespace FuzzyMatching

section Utils

@[specialize] private def iterateLookaround (f : (Option Char × Char × Option Char) → α) (string : String) : Array α :=
  if string.isEmpty then
    #[]
  else if string.length == 1 then
    #[f (none, string.get 0, none)]
  else Id.run do
    let mut result := Array.mkEmpty string.length
    result := result.push <| f (none, string.get 0, string.get ⟨1⟩)
    -- TODO: the following code is assuming all characters are ASCII
    for i in [2:string.length] do
      result := result.push <| f (string.get ⟨i - 2⟩, string.get ⟨i - 1⟩, string.get ⟨i⟩)
    result.push <| f (string.get ⟨string.length - 2⟩, string.get ⟨string.length - 1⟩, none)

private def containsInOrderLower (a b : String) : Bool := Id.run do
  if a.isEmpty then
    return true
  let mut aIt := a.mkIterator
    -- TODO: the following code is assuming all characters are ASCII
  for i in [:b.endPos.byteIdx] do
    if aIt.curr.toLower == (b.get ⟨i⟩).toLower then
      aIt := aIt.next
      if !aIt.hasNext then
        return true
  return false

end Utils


/-- Represents the type of a single character. -/
inductive CharType where
  | lower | upper | separator

def charType (c : Char) : CharType :=
  if c.isAlphanum then
    if c.isUpper
      then CharType.upper
      else CharType.lower
  else
    CharType.separator


/-- Represents the role of a character inside a word. -/
inductive CharRole where
  | head | tail | separator
  deriving Inhabited

@[inline] def charRole (prev? : Option CharType) (curr : CharType) (next?: Option CharType) : CharRole :=
  if curr matches CharType.separator then
    CharRole.separator
  else if prev?.isNone || prev? matches some CharType.separator then
    CharRole.head
  else if curr matches CharType.lower then
    CharRole.tail
  else if prev? matches some CharType.upper && !(next? matches some CharType.lower) then
    CharRole.tail
  else
    CharRole.head

/-- Add additional information to each character in a string. -/
private def stringInfo (s : String) : Array CharRole :=
  iterateLookaround (string := s) fun (prev?, curr, next?) =>
    charRole (prev?.map charType) (charType curr) (next?.map charType)


private def selectBest (missScore? matchScore? : Option Int) : Option Int :=
  match (missScore?, matchScore?) with
  | (missScore, none)  => missScore
  | (none, matchScore) => matchScore
  | (some missScore, some matchScore) =>
    some <| max missScore matchScore

/-- Match the given pattern with the given word. The algorithm uses dynamic
programming to find the best scores.

In addition to the current characters in the pattern and the word, the
algorithm uses different scores for the last operation (miss/match). This is
necessary to give consecutive character matches a bonus. -/
private def fuzzyMatchCore (pattern word : String) (patternRoles wordRoles : Array CharRole) : Option Int := Id.run do
  /- Flattened array where the value at index (i, j, k) represents the best possible score of a fuzzy match
  between the substrings pattern[:i+1] and word[:j+1] assuming that pattern[i] misses at word[j] (k = 0, i.e.
  it was matched earlier), or matches at word[j] (k = 1). A value of `none` corresponds to a score of -∞, and is used
  where no such match/miss is possible or for unneeded parts of the table. -/
  let mut result : Array (Option Int) := Array.replicate (pattern.length * word.length * 2) none
  let mut runLengths : Array Int := Array.replicate (pattern.length * word.length) 0

  -- penalty for starting a consecutive run at each index
  let mut startPenalties : Array Int := Array.replicate word.length 0

  let mut lastSepIdx := 0
  let mut penaltyNs : Int := 0
  let mut penaltySkip : Int := 0
  for wordIdx in [:word.length] do
    if (wordIdx != 0) && wordRoles[wordIdx]! matches .separator then
      -- reset skip penalty at namespace separator
      penaltySkip := 0
      -- add constant penalty for each namespace to prefer shorter namespace nestings
      penaltyNs := penaltyNs + 1
      lastSepIdx := wordIdx
    penaltySkip := penaltySkip + skipPenalty wordRoles[wordIdx]! (wordIdx == 0)
    startPenalties := startPenalties.set! wordIdx $ penaltySkip + penaltyNs

  -- TODO: the following code is assuming all characters are ASCII
  for patternIdx in [:pattern.length] do
    /- For this dynamic program to be correct, it's only necessary to populate a range of length
   `word.length - pattern.length` at each index (because at the very end, we can only consider fuzzy matches
    of `pattern` with a longer substring of `word`). -/
    for wordIdx in [patternIdx:word.length-(pattern.length - patternIdx - 1)] do
      let missScore? :=
        if wordIdx >= 1 then
          selectBest
            (getMiss result patternIdx (wordIdx - 1))
            (getMatch result patternIdx (wordIdx - 1))
        else none

      let mut matchScore? := none

      if allowMatch (pattern.get ⟨patternIdx⟩) (word.get ⟨wordIdx⟩) patternRoles[patternIdx]! wordRoles[wordIdx]! then
        if patternIdx >= 1 then
          let runLength := runLengths[getIdx (patternIdx - 1) (wordIdx - 1)]! + 1
          runLengths := runLengths.set! (getIdx patternIdx wordIdx) runLength

          matchScore? := selectBest
            (getMiss result (patternIdx - 1) (wordIdx - 1) |>.map (· + matchResult
              patternIdx wordIdx
              patternRoles[patternIdx]! wordRoles[wordIdx]!
              none
            - startPenalties[wordIdx]!))
            (getMatch result (patternIdx - 1) (wordIdx - 1) |>.map (· + matchResult
              patternIdx wordIdx
              patternRoles[patternIdx]! wordRoles[wordIdx]!
              (.some runLength)
            )) |>.map fun score => if wordIdx >= lastSepIdx then score + 1 else score -- main identifier bonus
        else
          runLengths := runLengths.set! (getIdx patternIdx wordIdx) 1
          matchScore? := .some $ matchResult
              patternIdx wordIdx
              patternRoles[patternIdx]! wordRoles[wordIdx]!
              none
              - startPenalties[wordIdx]!

      result := set result patternIdx wordIdx missScore? matchScore?

  return selectBest (getMiss result (pattern.length - 1) (word.length - 1)) (getMatch result (pattern.length - 1) (word.length - 1))

  where
    getDoubleIdx (patternIdx wordIdx : Nat) := patternIdx * word.length * 2 + wordIdx * 2

    getIdx (patternIdx wordIdx : Nat) := patternIdx * word.length + wordIdx

    getMiss (result : Array (Option Int)) (patternIdx wordIdx : Nat) : Option Int :=
      result[getDoubleIdx patternIdx wordIdx]!

    getMatch (result : Array (Option Int)) (patternIdx wordIdx : Nat) : Option Int :=
      result[getDoubleIdx patternIdx wordIdx + 1]!

    set (result : Array (Option Int)) (patternIdx wordIdx : Nat) (missValue matchValue : Option Int) : Array (Option Int) :=
      let idx := getDoubleIdx patternIdx wordIdx
      result |>.set! idx missValue |>.set! (idx + 1) matchValue

    /-- Heuristic to penalize skipping characters in the word. -/
    skipPenalty (wordRole : CharRole) (wordStart : Bool) : Int := Id.run do
      /- Skipping the beginning of the word. -/
      if wordStart then
        return 3
      /- Skipping the beginning of a segment. -/
      if wordRole matches CharRole.head then
        return 1

      return 0

    /-- Whether characters from the pattern and the word match. -/
    allowMatch (patternChar wordChar : Char) (patternRole wordRole : CharRole) : Bool := Id.run do
      /- Different characters do not match. -/
      if patternChar.toLower != wordChar.toLower then
        return false
      /- The beginning of a segment in the pattern must align with the beginning of a segment in the word. -/
      if patternRole matches CharRole.head && !(wordRole matches CharRole.head) then
        return false

      return true

    /-- Heuristic to rate a match. -/
    matchResult (patternIdx wordIdx : Nat) (patternRole wordRole : CharRole) (consecutive : Option Int) : Int := Id.run do
      let mut score : Int := 1
      /- Case-sensitive equality or beginning of a segment in pattern and word. -/
      if (pattern.get ⟨patternIdx⟩) == (word.get ⟨wordIdx⟩) || (patternRole matches CharRole.head && wordRole matches CharRole.head) then
        score := score + 1
      /- Matched end of word with end of pattern -/
      if wordIdx == word.length - 1 && patternIdx == pattern.length - 1 then
        score := score + 2
      /- Matched beginning of the word. -/
      if (wordIdx == 0) then
        score := score + 3
      /- Consecutive character match. -/
      if let some bonus := consecutive then
        /- consecutive run bonus -/
        score := score + bonus
      return score

/-- Match the given pattern with the given word using a fuzzy matching
algorithm. The resulting scores are in the interval `[0, 1]` or `none` if no
match was found. -/
def fuzzyMatchScore? (pattern word : String) : Option Float := Id.run do
  /- Some fast and simple checks. -/
  if pattern.isEmpty then
    return some 1
  if pattern.length > word.length then
    return none
  if !(containsInOrderLower pattern word) then
    return none

  let some score := fuzzyMatchCore pattern word (stringInfo pattern) (stringInfo word)
    | none
  let mut score := score

  /- Bonus if every character is matched. -/
  if pattern.length == word.length then
    score := score * 2

  /- Perfect score per character. -/
  let perfect := 4
  /- Perfect score for full match given the heuristic in `matchResult`;
  the latter term represents the bonus of a perfect consecutive run. -/
  let perfectMatch := (perfect * pattern.length + ((pattern.length * (pattern.length + 1) / 2) - 1))
  let normScore := Float.ofInt score / Float.ofInt perfectMatch

  return some <| min 1 (max 0 normScore)

def fuzzyMatchScoreWithThreshold? (pattern word : String) (threshold := 0.1) : Option Float :=
  fuzzyMatchScore? pattern word |>.filter (· > threshold)

/-- Match the given pattern with the given word using a fuzzy matching
algorithm. Return `false` if no match was found or the found match received a
score below the given threshold. -/
def fuzzyMatch (pattern word : String) (threshold := 0.2) : Bool :=
  fuzzyMatchScoreWithThreshold? pattern word threshold |>.isSome

end FuzzyMatching
end Lean
