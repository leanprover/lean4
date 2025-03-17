import Lean.Data.Trie

/-!

# Tests for the trie data structure

This test tests the `Lean.Parser.Trie` data structure by bisimulation with a simple `Array String`:
It performs a sequence of trie creation steps, and after each steps checks
whether the trie is operationally equivalent to the array of strings.

This test does not bother with values that are different than they `String` they are stored under.
This test does not test `upsert`; since `Trie.insert` goes through it, it should be sufficient
(and it would make this test approach more complicated.)
-/

open Lean.Data

/-- These keys used in `T.check` below. Also include keys for negative lookup tests here!  -/
def keys : Array String :=  #[
  "",
  "h",
  "hello",
  "helloo",
  "hellooo",
  "helloooooo",
  "hella",
  "hellx",
  "hö",
  "hü",
  "hä",
  "💩"
]

/-- A trie together with a reference value as an array of values -/
def T := Trie String × Array String

def T.empty : T := (.empty, .empty)

def T.insert : T → String → T := fun (t,a) s =>
  (t.insert s s, if a.contains s then a else a.push s)

/-- A convenience function for use in this test case -/
def Array.sorted : Array String → Array String := fun a =>
  a.qsort (fun s1 s2 => s1 < s2)

/-- The intended semanics of `Trie.findPrefix` -/
def Array.findPrefix : Array String → String → Array String := fun a s =>
  a.filter (fun s' => s.isPrefixOf s')

/-- The intended semanics of `Trie.matchPrefix`: Longest prefix found in trie -/
def Array.matchPrefix : Array String → String → Option String := fun a s => Id.run do
  for i in List.reverse (List.range (s.length + 1)) do
    let pfix := s.take i
    if let some _ := a.find? (· == pfix) then
      return some  pfix
  return none


def T.check : T → IO Unit := fun (t,a) => do
  -- Check lookup equivalence
  keys.forM fun s => do
    unless t.find? s = a.find? (· == s) do
      IO.println s!"find? differs: key = {s}"
  -- Check findPrefix equivalence
  keys.forM fun s => do
    unless (t.findPrefix s).sorted = (a.findPrefix s).sorted do
      IO.println s!"findPrefix differs: key = {s}"
  -- Check matchPrefix equivalence
  keys.forM fun s => do
    unless t.matchPrefix s 0 = a.matchPrefix s do
      IO.println s!"matchPrefix differs: key = {s}, got: {t.matchPrefix s 0} exp: {a.matchPrefix s} "
    let s' := "somePrefix" ++ s
    unless t.matchPrefix s' ((0 : String.Pos) + "somePrefix") = a.matchPrefix s do
      IO.println s!"matchPrefix differs (with prefix): key = {s}"

def main : IO Unit := do
  -- Add tricky insert sequences here:
  for seq in #[
    #["hello", "hella", "hellooo", "h", "hö", "hü", "💩", "", "hü"],
    #["", "helooooo"]
  ] do
    IO.println "Resetting trie"
    let mut t : T := T.empty
    t.check
    for s in seq do
      IO.println s!"Inserting {s}"
      t := t.insert s
      t.check
