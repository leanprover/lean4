type expr =
| Var of int
| Val of int
| Add of expr * expr
| Mul of expr * expr;;

let dec n =
  if n == 0 then 0 else n - 1;;

let rec mk_expr n v =
  if n == 0 then (if v == 0 then Var 1 else Val v)
  else Add (mk_expr (n-1) (v+1), mk_expr (n-1) (dec v));;

let rec append_add e1 e2 =
match (e1, e2) with
| (Add (e1, e2), e3) -> Add (e1, append_add e2 e3)
| (e1, e2)           -> Add (e1, e2);;

let rec append_mul e1 e2 =
match (e1, e2) with
| (Mul (e1, e2), e3) -> Mul (e1, append_mul e2 e3)
| (e1, e2)           -> Mul (e1, e2);;

let rec reassoc e =
match e with
| Add (e1, e2) ->
  let e1' = reassoc e1 in
  let e2' = reassoc e2 in
  append_add e1' e2'
| Mul (e1, e2) ->
  let e1' = reassoc e1 in
  let e2' = reassoc e2 in
  append_mul e1' e2'
| e -> e;;

let rec const_folding e =
match e with
| Add (e1, e2) ->
  let e1 = const_folding e1 in
  let e2 = const_folding e2 in
  (match (e1, e2) with
   | (Val a, Val b)          -> Val (a+b)
   | (Val a, Add (e, Val b)) -> Add (Val (a+b), e)
   | (Val a, Add (Val b, e)) -> Add (Val (a+b), e)
   | _                       -> Add (e1, e2))
| Mul (e1, e2) ->
  let e1 = const_folding e1 in
  let e2 = const_folding e2 in
  (match (e1, e2) with
   | (Val a, Val b)          -> Val (a*b)
   | (Val a, Mul (e, Val b)) -> Mul (Val (a*b), e)
   | (Val a, Mul (Val b, e)) -> Mul (Val (a*b), e)
   | _                       -> Mul (e1, e2))
| e ->  e;;

let rec size e =
match e with
| Add (e1, e2) -> size e1 + size e2 + 1
| Mul (e1, e2) -> size e1 + size e2 + 1
| e            -> 1;;

let rec eeval e =
 match e with
 | Val n -> n
 | Var x -> 0
 | Add (e1, e2) -> eeval e1 + eeval e2
 | Mul (e1, e2) -> eeval e1 * eeval e2;;

let e  = (mk_expr 23 1) in
let v1 = eeval e in
let v2 = eeval (const_folding (reassoc e)) in
Printf.printf "%8d %8d\n" v1 v2;;
