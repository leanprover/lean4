type color =
| Red
| Black;;

type node =
| Leaf
| Node of color * node * int * bool * node;;

let balance1 kv vv t n =
match n with
| Node (c, Node (Red, l, kx, vx, r1), ky, vy, r2) -> Node (Red, Node (Black, l, kx, vx, r1), ky, vy, Node (Black, r2, kv, vv, t))
| Node (c, l1, ky, vy, Node (Red, l2, kx, vx, r)) -> Node (Red, Node (Black, l1, ky, vy, l2), kx, vx, Node (Black, r, kv, vv, t))
| Node (c, l,  ky, vy, r)                         -> Node (Black, Node (Red, l, ky, vy, r), kv, vv, t)
| n -> Leaf;;

let balance2 t kv vv n =
match n with
| Node (_, Node (Red, l, kx1, vx1, r1), ky, vy, r2)  -> Node (Red, Node (Black, t, kv, vv, l), kx1, vx1, Node (Black, r1, ky, vy, r2))
| Node (_, l1, ky, vy, Node (Red, l2, kx2, vx2, r2)) -> Node (Red, Node (Black, t, kv, vv, l1), ky, vy, Node (Black, l2, kx2, vx2, r2))
| Node (_, l, ky, vy, r)                             -> Node (Black, t, kv, vv, Node (Red, l, ky, vy, r))
| n   -> Leaf;;

let is_red t =
match t with
| Node (Red, _, _, _, _) -> true
| _ -> false;;

let rec ins t kx vx =
match t with
| Leaf -> Node (Red, Leaf, kx, vx, Leaf)
| Node (Red, a, ky, vy, b) ->
  if kx < ky then Node (Red, ins a kx vx, ky, vy, b)
  else if ky = kx then Node (Red, a, kx, vx, b)
  else Node (Red, a, ky, vy, ins b kx vx)
| Node (Black, a, ky, vy, b) ->
  if kx < ky then
    (if is_red a then balance1 ky vy b (ins a kx vx)
      else Node (Black, (ins a kx vx), ky, vy, b))
  else if kx = ky then Node (Black, a, kx, vx, b)
  else if is_red b then balance2 a ky vy (ins b kx vx)
       else Node (Black, a, ky, vy, (ins b kx vx));;

let set_black n =
match n with
| Node (_, l, k, v, r) -> Node (Black, l, k, v, r)
| e                    -> e;;

let insert t k v =
if is_red t then set_black (ins t k v)
else ins t k v;;

let rec fold f n d =
match n with
| Leaf -> d
| Node(_, l, k, v, r) -> fold f r (f k v (fold f l d));;

let rec mk_map_aux freq n m r =
if n = 0 then m::r
else let n = n-1 in
     let m = insert m n (n mod 10 == 0) in
     let r = if n mod freq == 0 then m::r else r in
     mk_map_aux freq n m r;;

let mk_map n freq = mk_map_aux freq n Leaf [];;

let rec myLen n r =
match n with
| (Node (_, _, _, _, _) :: xs) -> myLen xs (r+1)
| (_ :: xs)      -> myLen xs r
| []             -> r;;

let main n freq =
let m = mk_map n freq in
let v = fold (fun k v r -> if v then r + 1 else r) (List.hd m) 0 in
Printf.printf "%d %d\n" (myLen m 0) v;
v;;

main (int_of_string Sys.argv.(1)) (int_of_string Sys.argv.(2));;
