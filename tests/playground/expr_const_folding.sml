datatype expr =
  Var of int
| Val of int
| Add of expr * expr
| Mul of expr * expr;;

fun dec n =
  if n = 0 then 0 else n - 1;;

fun mk_expr n v =
  if n = 0 then (if v = 0 then Var 1 else Val v)
  else Add (mk_expr (n-1) (v+1), mk_expr (n-1) (dec v));;

fun append_add e1 e2 =
case (e1, e2) of
  (Add (e1, e2), e3) => Add (e1, append_add e2 e3)
| (e1, e2)           => Add (e1, e2);;

fun append_mul e1 e2 =
case (e1, e2) of
  (Mul (e1, e2), e3) => Mul (e1, append_mul e2 e3)
| (e1, e2)           => Mul (e1, e2);;

fun reassoc e =
case e of
  Add (e1, e2) =>
  let val e1' = reassoc e1
  val e2' = reassoc e2 in
  append_add e1' e2' end
| Mul (e1, e2) =>
  let val e1' = reassoc e1
  val e2' = reassoc e2 in
  append_mul e1' e2' end
| e => e;;

fun const_folding e =
case e of
  Add (e1, e2) =>
  let val e1 = const_folding e1
  val e2 = const_folding e2 in
  (case (e1, e2) of
     (Val a, Val b)          => Val (a+b)
   | (Val a, Add (e, Val b)) => Add (Val (a+b), e)
   | (Val a, Add (Val b, e)) => Add (Val (a+b), e)
   | _                       => Add (e1, e2))
   end
| Mul (e1, e2) =>
  let val e1 = const_folding e1
  val e2 = const_folding e2 in
  (case (e1, e2) of
     (Val a, Val b)          => Val (a*b)
   | (Val a, Mul (e, Val b)) => Mul (Val (a*b), e)
   | (Val a, Mul (Val b, e)) => Mul (Val (a*b), e)
   | _                       => Mul (e1, e2))
   end
| e =>  e;;

fun size e =
case e of
  Add (e1, e2) => size e1 + size e2 + 1
| Mul (e1, e2) => size e1 + size e2 + 1
| e            => 1;;

fun eeval e =
 case e of
   Val n => n
 | Var x => 0
 | Add (e1, e2) => eeval e1 + eeval e2
 | Mul (e1, e2) => eeval e1 * eeval e2;;

val e  = (mk_expr 23 1)
val v1 = eeval e
val v2 = eeval (const_folding (reassoc e))
val _ = print (Int.toString v1 ^ " " ^ Int.toString v2 ^ "\n")
