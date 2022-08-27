def x := ["one", "two", "three"]

#eval x -- [one, two, three]

#eval "zero" :: x -- ["zero", "one", "two", "three"]

#eval x.cons "zero" -- ["zero", "one", "two", "three"]

#eval x.indexOf? "two" -- some 1

#eval x.find? (λ x => x == "three") -- some "three"

#eval x.any (λ x => x == "three") -- true

#eval x.append ["four", "five", "six"] -- ["one", "two", "three", "four", "five", "six"]

#eval ['e', 'l', 'e', 'p', 'h', 'a', 'n', 't'].asString -- "elephant"

#eval x.drop 1 -- ["two", "three"]

#eval x.take 2 -- ["one", "two"]

#eval x.map (λ x => x.length) -- [3, 3, 5]

#eval x.contains "three" -- true

#eval x.filter (λ x => x.startsWith "t") -- ["two", "three"]

#eval x.get! 2 -- "three"

#eval x[1]! -- "two"

#eval x.erase "two" -- ["one", "three"]

#eval x.head! -- "one"

#eval x.tail! -- ["two", "three"]

#eval ",".intercalate x -- "one,two,three"

#eval x.isEmpty -- false

#eval x.length -- 3

#eval [["a"], ["b"], ["c", "d"]].join -- ["a", "b", "c", "d"]

#eval x.reverse -- ["three", "two", "one"]

#eval x.removeAll ["two", "three"]  -- ["one"]

#eval x.replace "two" "2" -- ["one", "2", "three"]

#eval x.toArray -- #["one", "two", "three"]

#eval List.range 5 -- [0, 1, 2, 3, 4]

#eval x.zip (List.range 3) -- [("one", 0), ("two", 1), ("three", 2)]

#eval (x.zip (List.range 3)).unzip -- (["one", "two", "three"], [0, 1, 2])