type elem = int  (* pointer-tagged like in Lean, int32 would be actually boxed *)

let badRand (seed : elem) : elem = seed * 1664525 + 1013904223

let mkRandomArray (seed : elem) n =
  let s = ref seed in
  Array.init n (fun _ ->
    let seed = !s in
    s := badRand seed;
    seed)

exception Unsorted of string

let rec checkSortedAux (a : elem array) i =
  if i < Array.length a - 1 then begin
    if a.(i) > a.(i+1) then raise (Unsorted "array is not sorted");
    checkSortedAux a (i+1)
  end

let swap (arr : elem array) i j =
  let x = arr.(i) in
  let y = arr.(j) in
  arr.(i) <- y;
  arr.(j) <- x

let rec partitionAux hi pivot arr i j : int =
  if j < hi then
    if arr.(j) < pivot then begin
      swap arr i j;
      partitionAux hi pivot arr (i+1) (j+1)
    end else
      partitionAux hi pivot arr i (j+1)
  else begin
    swap arr i hi;
    i
  end

let partition arr lo hi =
  let mid = (lo + hi) / 2 in
  if arr.(mid) < arr.(lo) then swap arr lo mid;
  if arr.(hi)  < arr.(lo) then swap arr lo hi ;
  if arr.(mid) < arr.(hi) then swap arr mid hi;
  let pivot = arr.(hi) in
  partitionAux hi pivot arr lo lo

let rec qsortAux arr low high =
  if low < high then
    let mid = partition arr low high in
    qsortAux arr low mid;
    qsortAux arr (mid+1) high
  else ()

let qsort arr =
  qsortAux arr 0 (Array.length arr - 1)

let main n =
  for _ = 0 to n-1 do
    for i = 0 to n-1 do
      let xs = mkRandomArray i i in
      qsort xs;
      checkSortedAux xs 0
    done
  done;;

main (int_of_string Sys.argv.(1))
