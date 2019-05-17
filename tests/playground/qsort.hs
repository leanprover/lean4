import Control.Monad
import Control.Monad.ST
import Data.Array.IArray
import Data.Array.MArray
import Data.Array.ST
import Data.Word
import System.Environment

type Elem = Word32

badRand :: Elem -> Elem
badRand seed = seed * 1664525 + 1013904223

mkRandomArray :: Elem -> Int -> Array Int Elem
mkRandomArray seed n = listArray (0, n-1) $ take n $ iterate badRand seed

checkSortedAux :: Array Int Elem -> Int -> IO ()
checkSortedAux a i =
  if i < snd (bounds a) - 1 then do
    unless (a ! i <= a ! (i+1)) $ error "array is not sorted"
    checkSortedAux a (i+1)
  else
    pure ()

swap :: Int -> Int -> STArray s Int Elem -> ST s ()
swap i j arr = do
    x <- readArray arr i
    y <- readArray arr j
    writeArray arr i y
    writeArray arr j x

partitionAux as hi pivot i j =
  if j < hi then do
    a <- readArray as j
    if a < pivot then do
      swap i j as
      partitionAux as hi pivot (i+1) (j+1)
    else
      partitionAux as hi pivot i (j+1)
  else do
    swap i hi as
    pure i

partition :: STArray s Int Elem -> Int -> Int -> ST s Int
partition as lo hi = do
  let mid = (lo + hi) `div` 2
  amid <- readArray as mid
  alo <- readArray as lo
  if amid < alo then swap lo mid as else pure ()
  ahi <- readArray as hi
  alo <- readArray as lo
  if ahi < alo then swap lo hi as else pure ()
  amid <- readArray as mid
  ahi <- readArray as hi
  if amid < ahi then swap mid hi as else pure ()
  pivot <- readArray as hi
  partitionAux as hi pivot lo lo

qsortAux as low high =
  if low < high then do
    mid <- Main.partition as low high
    qsortAux as low mid
    qsortAux as (mid+1) high
  else pure ()

qsort :: STArray s Int Elem -> ST s ()
qsort as = do
  (low, high) <- getBounds as
  qsortAux as low high

main :: IO ()
main = do
  [n] <- getArgs >>= mapM readIO
  forM_ [0..n-1] $ \_ ->
    forM_ [0..n-1] $ \i -> do
      let xs = mkRandomArray (toEnum i) i
      let xs' = runSTArray (do
          mxs <- thaw xs
          qsort mxs
          pure mxs)
      --print xs'
      checkSortedAux xs' 0
