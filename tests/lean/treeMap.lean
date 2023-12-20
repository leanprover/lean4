inductive TreeNode :=
 | mkLeaf (name : String) : TreeNode
 | mkNode (name : String) (children : List TreeNode) : TreeNode

open TreeNode in def treeToList (t : TreeNode) : List String :=
 match t with
 | mkLeaf name => [name]
 | mkNode name children => name :: List.join (children.map treeToList)
termination_by t
