-- Test: constants used only in the type of a non-first member of a mutual block (#16133)
--
-- `Bool` occurs only in the type of `AB`, which has no constructors. When replay reaches the block
-- through `A`, it must still add `Bool` before adding the block.

mutual
inductive A : Prop where
  | mk : A
inductive AB : Bool → Prop where
end
