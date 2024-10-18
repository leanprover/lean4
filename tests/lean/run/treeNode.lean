inductive TreeNode :=
 | mkLeaf (name : String) : TreeNode
 | mkNode (name : String) (children : List TreeNode) : TreeNode

def treeToList (t : TreeNode) : List String :=
 match t with
 | .mkLeaf name => [name]
 | .mkNode name children => Id.run do
   let mut r := [name]
   for h : child in children do
     -- We will not this the following `have` in the future
     have : sizeOf child < 1 + sizeOf name + sizeOf children := Nat.lt_trans (List.sizeOf_lt_of_mem h) (by simp_arith)
     r := r ++ treeToList child
   return r

@[simp] theorem treeToList_eq (name : String) (children : List TreeNode) : treeToList (.mkNode name children) =  name :: List.join (children.map treeToList) := by
  simp [treeToList, Id.run, forIn, List.forIn]
  have : ∀ acc, (Id.run do List.forIn.loop (fun a b => ForInStep.yield (b ++ treeToList a)) children acc) = acc ++ List.join (List.map treeToList children) := by
    intro acc
    induction children generalizing acc with simp [List.forIn.loop, List.map, List.join, Id.run]
    | cons c cs ih => simp [Id.run] at ih; simp [ih, List.append_assoc]
  apply this

mutual
  def numNames : TreeNode → Nat
    | .mkLeaf _  => 1
    | .mkNode _ cs => 1 + numNamesLst cs
  def numNamesLst : List TreeNode → Nat
    | [] => 0
    | a :: as => numNames a + numNamesLst as
end

theorem length_treeToList_eq_numNames (t : TreeNode) : (treeToList t).length = numNames t := by
  match t with
  | .mkLeaf .. => simp [treeToList, numNames]
  | .mkNode _ cs => simp_arith [numNames, helper cs]
where
  helper (cs : List TreeNode) : (cs.map treeToList).join.length = numNamesLst cs := by
    match cs with
    | [] => simp [List.join, numNamesLst]
    | c::cs' => simp [List.join, List.map, numNamesLst, length_treeToList_eq_numNames c, helper cs']
