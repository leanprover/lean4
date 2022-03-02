inductive MyProduct (A: Type) (B: Type): Type
  | mk: A -> B -> MyProduct A B

inductive MyTree: Type
  | leaf: MyTree
  | node: MyProduct MyTree MyTree -> MyTree

def my_length: MyTree -> Nat
  | MyTree.leaf => 0
  | MyTree.node (MyProduct.mk left right) => 1 + my_length left + my_length right
