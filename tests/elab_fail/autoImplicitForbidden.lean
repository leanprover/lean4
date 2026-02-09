def f : f → Bool := -- Error at second `f`
  fun _ => true

mutual

  def g : h → Bool := -- Error at `h`, `h` is not eligible to be an auto implicit because of the mutual block
    fun _ => true

  def h := List Nat

end

structure Bla (x : List Bla) where -- Error at second `Foo`
  val : Nat

inductive Foo : List Foo -> Type -- Error at second `Foo`
  | x : Foo []

mutual
  inductive Ex1 : Ex2 → Type -- Error at `Ex2`

  inductive Ex2 : Type
end


structure Bar :=
  (x : Na)
  (y : Nat := foobar)  -- Error at `foobar`

#print Bar.mk
