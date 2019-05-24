open Array
type elem = Word32.word

fun badRand (seed : elem) : elem = (seed * Word32.fromInt 1664525) + Word32.fromInt 1013904223

fun mkRandomArray (seed : elem) n =
  let val s = ref seed in
  tabulate (n, fn _ =>
    let val seed = (!s) in
    s := badRand seed;
    seed
    end)
  end

exception Unsorted of string

fun checkSortedAux (a : elem array) i =
  if i < Array.length a - 1 then (
    if sub (a, i) > sub (a, i+1) then raise (Unsorted "array is not sorted") else ();
    checkSortedAux a (i+1)
  ) else ()

fun swap (arr : elem array) i j =
  let
    val x = sub (arr, i)
    val y = sub (arr, j) in
  (update (arr, i, y); update (arr, j, x))
  end

fun partitionAux hi pivot arr i j : int =
  if j < hi then (
    if sub (arr, j) < pivot then (
      swap arr i j;
      partitionAux hi pivot arr (i+1) (j+1)
    ) else
      partitionAux hi pivot arr i (j+1)
  ) else (
    swap arr i hi;
    i
  )

fun partition arr lo hi =
  let val mid = (lo + hi) div 2 in (
  if sub (arr, mid) < sub (arr, lo) then swap arr lo mid else ();
  if sub (arr, hi)  < sub (arr, lo) then swap arr lo hi  else ();
  if sub (arr, mid) < sub (arr, hi) then swap arr mid hi else ();
  let val pivot = sub (arr, hi) in
  partitionAux hi pivot arr lo lo
  end)
  end

fun qsortAux arr low high =
  if low < high then
    let val mid = partition arr low high in
    (qsortAux arr low mid;
     qsortAux arr (mid+1) high)
    end
  else ()

fun qsort arr =
  qsortAux arr 0 (Array.length arr - 1)

fun for (start, stop, f) =
let
  fun loop i = if i = stop then () else (f i; loop (i + 1))
in
  loop start
end

fun main n =
  for (0, n-1, fn _ =>
    for (0, n-1, fn i =>
      let val xs = mkRandomArray (Word32.fromInt i) i in
      (qsort xs;
      checkSortedAux xs 0)
      end
    )
  )

val _ = main ((valOf o Int.fromString o List.hd o CommandLine.arguments) ())
