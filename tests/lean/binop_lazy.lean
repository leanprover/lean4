class HOrElse' (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hOrElse' : α → (Unit → β) → γ

infixr:20  " <%> " => HOrElse.hOrElse'

macro_rules | `($x <%> $y) => `(binop_lazy% HOrElse'.hOrElse' $x $y)

instance : HOrElse' (IO α) (IO α) (IO α) where
  hOrElse' a b := try a catch _ => b ()

def f : IO Unit :=
  (do IO.println "case 1"; throw (IO.userError "failed"))
  <%>
  (do IO.println "case 2"; throw (IO.userError "failed"))
  <%>
  (do IO.println "case 3")
  <%>
  (let x := dbg_trace "hello"; 1
   IO.println x)

#eval f -- should not print hello
