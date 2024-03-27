-- Testing functional induction derivation with mutual recursion + dependent types
inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite

abbrev Finite.asType : Finite → Type
  | .unit => Unit
  | .bool => Bool
  | .pair t1 t2 => asType t1 × asType t2
  | .arr t1 t2 => asType t1 → asType t2

def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse

mutual
def Finite.enumerate (t : Finite) : List t.asType :=
  match t with
  | .unit => [()]
  | .bool => [true, false]
  | .pair t1 t2 => t1.enumerate.product t2.enumerate
  | .arr t1 t2 => t1.functions t2.enumerate

def Finite.functions (t : Finite) (results : List α) : List (t.asType → α) :=
  match t with
  | .unit => results.map fun r => fun () => r
  | .bool =>
    (results.product results).map fun (r1, r2) =>
      fun
      | true => r1
      | false => r2
  | .pair t1 t2 =>
    let f1s := t1.functions <| t2.functions results
    f1s.map fun f => fun (x, y) => f x y
  | .arr t1 t2 =>
    let args := t1.enumerate
    let base := results.map fun r => fun _ => r
    args.foldr (init := base) fun arg rest =>
      (t2.functions rest).map fun (more : t2.asType → (t1.asType → t2.asType) → α) =>
        fun (f : t1.asType → t2.asType) => more (f arg) f
end

/--
info: Finite.functions.induct (motive1 : Finite → Prop) (motive2 : (α : Type) → Finite → List α → Prop)
  (case1 : motive1 Finite.unit) (case2 : motive1 Finite.bool)
  (case3 : ∀ (t1 t2 : Finite), motive1 t1 → motive1 t2 → motive1 (t1.pair t2))
  (case4 : ∀ (t1 t2 : Finite), motive1 t2 → motive2 t2.asType t1 t2.enumerate → motive1 (t1.arr t2))
  (case5 : ∀ (α : Type) (results : List α), motive2 α Finite.unit results)
  (case6 : ∀ (α : Type) (results : List α), motive2 α Finite.bool results)
  (case7 :
    ∀ (α : Type) (results : List α) (t1 t2 : Finite),
      motive2 α t2 results → motive2 (t2.asType → α) t1 (t2.functions results) → motive2 α (t1.pair t2) results)
  (case8 :
    ∀ (α : Type) (results : List α) (t1 t2 : Finite),
      motive1 t1 →
        (∀ (rest : List ((t1.arr t2).asType → α)), motive2 ((t1.arr t2).asType → α) t2 rest) →
          motive2 α (t1.arr t2) results)
  (α : Type) (t : Finite) (results : List α) : motive2 α t results
-/
#guard_msgs in
#check Finite.functions.induct
