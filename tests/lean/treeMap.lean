-- Until stage0 update
attribute [auto_attach]
  List.map_wfParam
  List.map_unattach
  List.filter_wfParam
  List.filter_unattach
  List.reverse_wfParam
  List.reverse_unattach
  List.foldl_wfParam
  List.foldl_unattach
  Array.map_wfParam
  Array.map_unattach

inductive TreeNode where
 | mkLeaf (name : String) : TreeNode
 | mkNode (name : String) (children : List TreeNode) : TreeNode

open TreeNode in def treeToList (t : TreeNode) : List String :=
 match t with
 | mkLeaf name => [name]
 | mkNode name children => name :: List.flatten (children.map treeToList)
termination_by t
