--
-- The Computer Language Benchmarks Game
-- https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
--
-- Contributed by Don Stewart
-- Basic parallelization by Roman Kashitsyn
-- Tail call optimizations by Izaak Weiss
--

import System.Environment
import Data.Bits
import Text.Printf
import Control.Parallel.Strategies

--
-- an artificially strict tree. 
--
-- normally you would ensure the branches are lazy, but this benchmark
-- requires strict allocation.
--
data Tree = Nil | Node !Tree !Tree

minN = 4

io s n t = printf "%s of depth %d\t check: %d\n" s n t

main = do
    n <- getArgs >>= readIO . head
    let maxN     = max (minN + 2) n
        stretchN = maxN + 1

    -- stretch memory tree
    let c = check (make stretchN)
    io "stretch tree" stretchN c

    -- allocate a long lived tree
    let !long    = make maxN

    -- allocate, walk, and deallocate many bottom-up binary trees
    let vs = (depth minN maxN) `using` (parList $ evalTuple3 r0 r0 rseq)
    mapM_ (\((m,d,i)) -> io (show m ++ "\t trees") d i) vs

    -- confirm the long-lived binary tree still exists
    io "long lived tree" maxN (check long)

-- generate many trees
depth :: Int -> Int -> [(Int, Int, Int)]
depth d m
    | d <= m    = (n, d, sumT d n 0) : depth (d+2) m
    | otherwise = []
  where n = 1 `shiftL` (m - d + minN)

-- allocate and check lots of trees
sumT :: Int -> Int -> Int -> Int
sumT d 0 t = t
sumT d i t = sumT d (i-1) (t + a)
  where a = check (make d)

-- traverse the tree, counting up the nodes
check :: Tree -> Int
check t = tailCheck t 0

tailCheck :: Tree -> Int -> Int
tailCheck Nil        !a = a
tailCheck (Node l r) !a = tailCheck l $ tailCheck r $ a + 1

-- build a tree
make :: Int -> Tree
make d = make' d d

-- This function has an extra argument to suppress the
-- Common Sub-expression Elimination optimization
make' :: Int -> Int -> Tree
make' _  0 = Node Nil Nil
make' !n d = Node (make' (n - 1) (d - 1)) (make' (n + 1) (d - 1))
