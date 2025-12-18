(* from https://smlnj-gitlab.cs.uchicago.edu/manticore/benchmarks/blob/master/benchmarks/programs/shootout-binarytrees/binarytrees.mlton-2.sml *)
(* adjusted to match computation of other versions *)
(* binarytrees.mlton
 *
 * The Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * Contributed by Troestler Christophe
 * Ported to MLton/SML by sweeks@sweeks.com.
 * Optimized and compressed by Vesa Karvonen.
 * De-optimized by Isaac Gouy
 *)
datatype tree = Nil | Node of tree * tree
fun mk 0 = Node (Nil, Nil) | mk d = Node (mk (d-1), mk (d-1))
fun chk Nil = 0 | chk (Node (l, r)) = 1 + chk l + chk r
val n = valOf (Int.fromString (hd (CommandLine.arguments ()))) handle _ => 10
val min' = 4
val max' = Int.max (min' + 2, n)
val stretch' = max' + 1
fun msg h d t = app print [h, Int.toString d, "\t check: ", Int.toString t, "\n"]
val () = msg "stretch tree of depth " stretch' (chk (mk stretch'))
val longLivedTree = mk max'
fun loopDepths d =
    if d > max' then ()
    else let val n = Word.toInt (Word.<< (0w1, Word.fromInt (max'-d+min')))
             fun lp (i, c) = if i>n then c
                             else lp (i+1, c + chk (mk d))
         in msg (Int.toString n^"\t trees of depth ") d (lp (1, 0))
          ; loopDepths (d + 2) end
val () = loopDepths min'
val () = msg "long lived tree of depth " max' (chk longLivedTree)
