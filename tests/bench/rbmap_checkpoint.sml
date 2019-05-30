datatype color =
  Red
| Black;;

datatype node =
  Leaf
| Node of color * node * int * bool * node;;

fun balance1 kv vv t n =
case n of
  Node (c, Node (Red, l, kx, vx, r1), ky, vy, r2) => Node (Red, Node (Black, l, kx, vx, r1), ky, vy, Node (Black, r2, kv, vv, t))
| Node (c, l1, ky, vy, Node (Red, l2, kx, vx, r)) => Node (Red, Node (Black, l1, ky, vy, l2), kx, vx, Node (Black, r, kv, vv, t))
| Node (c, l,  ky, vy, r)                         => Node (Black, Node (Red, l, ky, vy, r), kv, vv, t)
| n => Leaf;;

fun balance2 t kv vv n =
case n of
  Node (_, Node (Red, l, kx1, vx1, r1), ky, vy, r2)  => Node (Red, Node (Black, t, kv, vv, l), kx1, vx1, Node (Black, r1, ky, vy, r2))
| Node (_, l1, ky, vy, Node (Red, l2, kx2, vx2, r2)) => Node (Red, Node (Black, t, kv, vv, l1), ky, vy, Node (Black, l2, kx2, vx2, r2))
| Node (_, l, ky, vy, r)                             => Node (Black, t, kv, vv, Node (Red, l, ky, vy, r))
| n   => Leaf;;

fun is_red t =
case t of
  Node (Red, _, _, _, _) => true
| _ => false;;

fun ins t kx vx =
case t of
  Leaf => Node (Red, Leaf, kx, vx, Leaf)
| Node (Red, a, ky, vy, b) =>
  if kx < ky then Node (Red, ins a kx vx, ky, vy, b)
  else if ky = kx then Node (Red, a, kx, vx, b)
  else Node (Red, a, ky, vy, ins b kx vx)
| Node (Black, a, ky, vy, b) =>
  if kx < ky then
    (if is_red a then balance1 ky vy b (ins a kx vx)
      else Node (Black, (ins a kx vx), ky, vy, b))
  else if kx = ky then Node (Black, a, kx, vx, b)
  else if is_red b then balance2 a ky vy (ins b kx vx)
       else Node (Black, a, ky, vy, (ins b kx vx));;

fun set_black n =
case n of
  Node (_, l, k, v, r) => Node (Black, l, k, v, r)
| e                    => e;;

fun insert t k v =
if is_red t then set_black (ins t k v)
else ins t k v;;

fun fold f n d =
case n of
  Leaf => d
| Node(_, l, k, v, r) => fold f r (f k v (fold f l d));;

fun mk_map_aux freq n m r =
if n = 0 then m::r
else let val n = n-1
       val m = insert m n (n mod 10 = 0)
       val r = if n mod freq = 0 then m::r else r in
     mk_map_aux freq n m r
     end

fun mk_map n freq = mk_map_aux freq n Leaf [];;

fun mylen m r =
case m of
  [] => r
| (x::xs) =>
  case x of
    Node _ => mylen xs (r + 1)
  | _ => mylen xs r;;

fun main n freq =
let
  val m = mk_map n freq
  val v = fold (fn k => fn v => fn r => if v then r + 1 else r) (List.hd m) 0 in
print (Int.toString (mylen m 0) ^ " " ^ Int.toString v)
end

val l = List.map (valOf o Int.fromString) (CommandLine.arguments ())
val _ = main (List.nth (l, 0)) (List.nth (l, 1))
