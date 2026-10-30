module

import all Lean.EnvExtension
import Init.Data.UInt.Lemmas

/-!
Test the USize and Nat name searches against Array.binSearch, including empty arrays, missing
names, numeric and nested names, and duplicate keys whose values distinguish the selected probe.
-/

open Lean

private def checkSearches (entries : Array (Name × Nat)) (queries : Array Name) : IO Unit := do
  let entries := entries.qsort (fun a b => Name.quickLt a.1 b.1)
  let names := entries.map (·.1)
  for query in queries do
    let expected := entries.binSearch (query, 0) (fun a b => Name.quickLt a.1 b.1)
    unless findSortedByName? entries query == expected do
      throw <| IO.userError s!"findSortedByName? differs: size={entries.size}, query={query}"
    unless containsSortedName names query == expected.isSome do
      throw <| IO.userError s!"containsSortedName differs: size={entries.size}, query={query}"
    if h : 0 < entries.size then
      let actual := findSortedByName?.go entries query 0 (entries.size - 1) (by omega) (by omega)
      unless actual == expected do
        throw <| IO.userError s!"Nat lookup differs: size={entries.size}, query={query}"
      let actual := containsSortedName.go names query 0 (names.size - 1)
        (by simp only [names, Array.size_map]; omega) (by simp only [names, Array.size_map]; omega)
      unless actual == expected.isSome do
        throw <| IO.userError s!"Nat membership differs: size={entries.size}, query={query}"
      if hb : entries.size < 2147483647 then
        let hi := USize.ofNat32 (entries.size - 1) (by omega)
        let actual := findSortedByName?.goUSize entries query hb 0 hi
          (by simp [hi]) (by simp [hi]; omega)
        unless actual == expected do
          throw <| IO.userError s!"USize lookup differs: size={entries.size}, query={query}"
        let actual := containsSortedName.goUSize names query (by simpa [names] using hb) 0 hi
          (by simp [hi]) (by simp [hi, names]; omega)
        unless actual == expected.isSome do
          throw <| IO.userError s!"USize membership differs: size={entries.size}, query={query}"

#eval do
  let mut pool : Array Name := #[.anonymous, `a, `a.b, `a.b.c, `α, `«a.b», .num .anonymous 0]
  for i in [:32] do
    pool := pool.push (.num `prefix i)
    pool := pool.push (.str `prefix s!"name{i}")
    pool := pool.push (.str (.num `prefix i) "suffix")
  let queries := pool ++ #[`missing, `prefix.missing, .num `prefix 1000000]
  for size in [:65] do
    for stride in #[0, 1, 3, 17] do
      checkSearches ((Array.range size).map fun i => (pool[(i * stride) % pool.size]!, i)) queries
    checkSearches ((Array.range size).map fun i => (pool[(i / 3) % pool.size]!, i)) queries
  for size in #[127, 128, 129, 255, 256, 257, 1023, 1024, 1025] do
    checkSearches ((Array.range size).map fun i => (.num `large i, i))
      #[.num `large 0, .num `large (size / 2), .num `large (size - 1), .num `large size]
