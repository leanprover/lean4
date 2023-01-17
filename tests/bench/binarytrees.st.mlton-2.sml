(* from https://smlnj-gitlab.cs.uchicago.edu/manticore/benchmarks/blob/master/benchmarks/programs/shootout-binarytrees/binarytrees.mlton-2.sml *)
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
datatype 'a tree = Nil | Node of 'a tree * 'a * 'a tree
(* fun mk 0 i = Nil | mk d i = Node (mk (d-1) (i*2-1), i, mk (d-1) (i*2)) *)
fun mk 0 i = Node (Nil, i, Nil) | mk d i = Node (mk (d-1) (i*2-1), i, mk (d-1) (i*2))
fun chk Nil = 0 | chk (Node (l, i, r)) = i + chk l - chk r
val n = valOf (Int.fromString (hd (CommandLine.arguments ()))) handle _ => 10
val min' = 4
val max' = Int.max (min' + 2, n)
val stretch' = max' + 1
val i2s = String.translate (fn #"~" => "-" | c => str c) o Int.toString
fun msg h d t = app print [h, Int.toString d, "\t check: ", i2s t, "\n"]
val () = msg "stretch tree of depth " stretch' (chk (mk stretch' 0))
val longLivedTree = mk max' 0
fun loopDepths d =
    if d > max' then ()
    else let val n = Word.toInt (Word.<< (0w1, Word.fromInt (max'-d+min')))
             fun lp (i, c) = if i=n then c
                             else lp (i+1, c + chk (mk d i) + chk (mk d (~i)))
         in msg (Int.toString (2*n)^"\t trees of depth ") d (lp (0, 0))
          ; loopDepths (d + 2) end
val () = loopDepths min'
val () = msg "long lived tree of depth " max' (chk longLivedTree)
