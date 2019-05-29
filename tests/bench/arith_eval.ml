type expr =
| Var of int
| Val of int
| Add of expr * expr;;

let dec n =
  if n == 0 then 0 else n - 1;;

let rec mk_expr n v =
  if n == 0 then Val v
  else Add (mk_expr (n-1) (v+1), mk_expr (n-1) (dec v));;

let rec eeval e =
 match e with
 | Val n -> n
 | Var x -> 0
 | Add (l, r) -> eeval l + eeval r;;

Printf.printf "%8d\n" (eeval (mk_expr 26 1));;
