def map (f : α → Option β) (as : List α) : List β :=
  Id.run <| as.filterMapM (pure <| f ·)

theorem map_some {xs : List α} : map some xs = xs := by
  sorry

theorem map_map {f : α → Option β} {g : β → Option γ} {xs : List α} :
    map g (map f xs) = map (fun x => (f x).bind g) xs := by
  sorry

grind_pattern map_map => map g (map f xs) where
  f =/= some
  g =/= some

/-- trace: [grind.ematch.instance] map_some: map some xs = xs -/
#guard_msgs (drop error, trace) in
set_option trace.grind.ematch.instance true in
example (xs : List Nat) (h : map some xs = ys) : False := by
  grind only [= map_some, usr map_map]

theorem extract_empty {start stop : Nat} : (#[] : Array α).extract start stop = #[] :=
  Array.extract_empty_of_size_le_start (Nat.zero_le _)

theorem extract_extract {as : Array α} {i j k l : Nat} :
    (as.extract i j).extract k l = as.extract (i + k) (min (i + l) j) := by
  apply Array.extract_extract

grind_pattern extract_extract => (as.extract i j).extract k l where
  as =/= #[]

/-- trace: [grind.ematch.instance] extract_empty: #[].extract i j = #[] -/
#guard_msgs (drop error, trace) in
set_option trace.grind.ematch.instance true in
example (as : Array Nat) (h : #[].extract i j = as) : False := by
  grind only [= extract_empty, usr extract_extract]

#guard_msgs (warning, drop error) in
example (as bs : List Nat) (h : as.filterMap some = bs) : False := by
  grind (instances := 50) [= List.filterMap_filterMap] -- No warning because stdlib version has a constraint

#guard_msgs (warning, drop error) in
example (as bs : List Nat) (h : as.filterMap some = bs) : False := by
  grind (instances := 50) [List.filterMap_filterMap] -- No warning because stdlib version has a constraint
