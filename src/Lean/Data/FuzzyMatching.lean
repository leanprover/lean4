/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Lars König

The string fuzzy matching algorithm in this file is based on the algorithm
used in LLVM with some modifications. The LLVM algorithm itself is based on VS
code's client side filtering algorithm.
-/

namespace Lean
namespace FuzzyMatching


section Utils

@[specialize] private def iterateLookaround (f : (Option Char × Char × Option Char) → α) (string : String) : Array α :=
  if string.isEmpty then
    #[]
  else if string.length == 1 then
    #[f (none, string.get 0, none)]
  else Id.run <| do
    let mut result := Array.mkEmpty string.length
    result := result.push <| f (none, string.get 0, string.get 1)

    for i in [2:string.length] do
      result := result.push <| f (string.get (i - 2), string.get (i - 1), string.get i)
    result.push <| f (string.get (string.length - 2), string.get (string.length - 1), none)

private def containsInOrderLower (a b : String) : Bool := Id.run <| do
  if a.isEmpty then
    return true
  let mut aIt := a.mkIterator
  for i in [:b.bsize] do
    if aIt.curr.toLower == (b.get i).toLower then
      aIt := aIt.next
      if !aIt.hasNext then
        return true
  return false

end Utils


/- Represents the type of a single character. -/
inductive CharType where
  | lower | upper | separator

def charType (c : Char) : CharType :=
  if c.isAlphanum then
    if c.isUpper
      then CharType.upper
      else CharType.lower
  else
    CharType.separator


/- Represents the role of a character inside a word. -/
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

/- Add additional information to each character in a string. -/
private def stringInfo (s : String) : Array CharRole :=
  iterateLookaround (string := s) fun (prev?, curr, next?) =>
    charRole (prev?.map charType) (charType curr) (next?.map charType)


private def selectBest (missScore? matchScore? : Option Int) : Option Int :=
  match (missScore?, matchScore?) with
  | (missScore, none)  => missScore
  | (none, matchScore) => matchScore
  | (some missScore, some matchScore) =>
    some <| max missScore matchScore

/- Match the given pattern with the given word. The algorithm uses dynamic
programming to find the best scores.

In addition to the current characters in the pattern and the word, the
algorithm uses different scores for the last operation (miss/match). This is
necessary to give consecutive character matches a bonus. -/
private def fuzzyMatchCore (pattern word : String) (patternRoles wordRoles : Array CharRole) : Option Int := Id.run <| do
  let mut result : Array (Option Int) := Array.mkArray ((pattern.length + 1) * (word.length + 1) * 2) none

  result := set result 0 0 (some 0) none

  let mut penalty := 0
  for wordIdx in [:word.length - pattern.length] do
    penalty := penalty - skipPenalty (wordRoles.get! wordIdx) false (wordIdx == 0)
    result := set result 0 (wordIdx+1) (some penalty) none

  for patternIdx in [:pattern.length] do
    let patternComplete := patternIdx == pattern.length - 1

    for wordIdx in [patternIdx:word.length-(pattern.length - patternIdx - 1)] do
      let missScore? := selectBest
        (getMiss result (patternIdx + 1) wordIdx)
        (getMatch result (patternIdx + 1) wordIdx)
        |>.map (· - skipPenalty (wordRoles.get! wordIdx) patternComplete (wordIdx == 0))

      let matchScore? :=
        if allowMatch (pattern.get patternIdx) (word.get wordIdx) (patternRoles.get! patternIdx) (wordRoles.get! wordIdx) then
          selectBest
            (getMiss result patternIdx wordIdx |>.map (· + matchResult
              (pattern.get patternIdx) (word.get wordIdx)
              (patternRoles.get! patternIdx) (wordRoles.get! wordIdx)
              false
              (wordIdx == 0)
            ))
            (getMatch result patternIdx wordIdx |>.map (· + matchResult
              (pattern.get patternIdx) (word.get wordIdx)
              (patternRoles.get! patternIdx) (wordRoles.get! wordIdx)
              true
              (wordIdx == 0)
            ))
        else none

      result := set result (patternIdx + 1) (wordIdx + 1) missScore? matchScore?

  return selectBest (getMiss result pattern.length word.length) (getMatch result pattern.length word.length)

  where
    getMiss (result : Array (Option Int)) (patternIdx wordIdx : Nat) : Option Int :=
      let idx := patternIdx * (word.length + 1) * 2 + wordIdx * 2
      result.get! idx

    getMatch (result : Array (Option Int)) (patternIdx wordIdx : Nat) : Option Int :=
      let idx := patternIdx * (word.length + 1) * 2 + wordIdx * 2 + 1
      result.get! idx

    set (result : Array (Option Int)) (patternIdx wordIdx : Nat) (missValue matchValue : Option Int) : Array (Option Int) :=
      let idx := patternIdx * (word.length + 1) * 2 + wordIdx * 2
      result |>.set! idx missValue |>.set! (idx + 1) matchValue

    /- Heuristic to penalize skipping characters in the word. -/
    skipPenalty (wordRole : CharRole) (patternComplete : Bool) (wordStart : Bool) : Int := Id.run <| do
      /- Skipping characters if the match is already completed is free. -/
      if patternComplete then
        return 0
      /- Skipping the beginning of the word. -/
      if wordStart then
        return 3
      /- Skipping the beginning of a segment. -/
      if wordRole matches CharRole.head then
        return 1

      return 0

    /- Whether characters from the pattern and the word match. -/
    allowMatch (patternChar wordChar : Char) (patternRole wordRole : CharRole) : Bool := Id.run <| do
      /- Different characters do not match. -/
      if patternChar.toLower != wordChar.toLower then
        return false
      /- The beginning of a segment in the pattern must align with the beginning of a segment in the word. -/
      if patternRole matches CharRole.head && !(wordRole matches CharRole.head) then
        return false

      return true

    /- Heuristic to rate a match. -/
    matchResult (patternChar wordChar : Char) (patternRole wordRole : CharRole) (consecutive : Bool) (wordStart : Bool) : Int := Id.run <| do
      let mut score := 1
      /- Case-sensitive equality or beginning of a segment in pattern and word. -/
      if patternChar == wordChar || (patternRole matches CharRole.head && wordRole matches CharRole.head) then
        score := score + 1
      /- Beginning of the word or consecutive character match. -/
      if wordStart || consecutive then
        score := score + 2
      /- Match starts in the middle of a segment. -/
      if wordRole matches CharRole.tail && !consecutive then
        score := score - 3
      /- Beginning of a segment in the pattern is not aligned with the
      beginning of a segment in the word. -/
      if patternRole matches CharRole.head && wordRole matches CharRole.tail then
        score := score - 1

      return score

/- Match the given pattern with the given word using a fuzzy matching
algorithm. The resulting scores are in the interval `[0, 1]` or `none` if no
match was found. -/
def fuzzyMatchScore? (pattern word : String) : Option Float := Id.run <| do
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

  /- Perfect score per character given the heuristic in `matchResult`. -/
  let perfect := 4
  let normScore := Float.ofInt score / Float.ofInt (perfect * pattern.length)

  return some <| min 1 (max 0 normScore)

def fuzzyMatchScoreWithThreshold? (pattern word : String) (threshold := 0.2) : Option Float :=
  fuzzyMatchScore? pattern word |>.filter (· > threshold)

/- Match the given pattern with the given word using a fuzzy matching
algorithm. Return `false` if no match was found or the found match received a
score below the given threshold. -/
def fuzzyMatch (pattern word : String) (threshold := 0.2) : Bool :=
  fuzzyMatchScoreWithThreshold? pattern word threshold |>.isSome

end FuzzyMatching
end Lean
