/- Underapplying a projection notation applies the 'this' argument to the wrong parameter.
   It should either fail or (preferably) construct an explicit lambda. -/

-- Char → Bool
#check fun c => ['a', 'b'].elem c
-- List (List Char) → Bool
#check ['a', 'b'].elem
-- works
#check fun (s : String) => s.split (fun c => ['a', 'b'].elem c)
-- doesn't work
#check fun (s : String) => s.split (['a', 'b'].elem)
