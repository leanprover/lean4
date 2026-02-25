/-!
# Testing named parent projections for `structure`s
-/

structure S where

structure S' extends toParent : S where
                     --^ textDocument/hover
