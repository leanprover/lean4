inductive TreeNode where
 | mkLeaf (name : String) : TreeNode
 | mkNode (name : String) (children : List TreeNode) : TreeNode

open TreeNode in def treeToList (t : TreeNode) : List String :=
 match t with
 | mkLeaf name => [name]
 | mkNode name children => name :: List.flatten (children.map treeToList)
termination_by t
