def rowStr1 : Array Bool → String := Array.foldr (fun b s => s ++ (if b then "#" else " ")) ""
def rowStr2 : List Bool → String := List.foldr (fun b s => s ++ (if b then "#" else " ")) ""
def rowStr3 (as : Array Bool) : String := as.foldr (fun b s => s ++ (if b then "#" else " ")) ""
def rowStr4 (as : List Bool) : String := as.foldr (fun b s => s ++ (if b = true then "#" else " ")) ""
def rowStr5 : Array Bool → String := fun as => Array.foldr (fun b s => s ++ (if b then "#" else " ")) "" as
def rowStr6 : List Bool → String := fun as => List.foldr (fun b s => s ++ (if b then "#" else " ")) "" as
